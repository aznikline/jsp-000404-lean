import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_20_11_13_M_LR_L_I_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
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
  have h3ehi := hb3.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0ehi5 := h0ehi (m.d 0 1) (by simp)
  have u0ehi6 := h0ehi (m.d 0 2) (by simp)
  have u0ehi7 := h0ehi (m.d 0 3) (by simp)
  have u0ehi8 := h0ehi (m.d 0 4) (by simp)
  have u0ehi9 := h0ehi (m.d 0 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 3 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 4 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 1 2 3 (by decide) (by decide) with h7 | h7
                · linarith only [h0, h7, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h9 | h9
                  · linarith only [h0, h4, h7, h9, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h11 | h11
                    · linarith only [h0, h11, h4, h7, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h13 | h13
                      · linarith only [h0, h13, h4, h7, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h15 | h15
                        · linarith only [h0, h15, h4, h7, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi4]
                        · linarith only [h0, h15, h4, h5, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi1]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h18 | h18
                · linarith only [h0, h18, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h20 | h20
                  · linarith only [h0, h18, h20, h4, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h22 | h22
                    · linarith only [h0, h18, h22, h4, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h24 | h24
                      · linarith only [h1, h24, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h26 | h26
                        · linarith only [h0, h18, h26, h4, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi4]
                        · linarith only [h0, h26, h4, h5, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi1]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h29 | h29
              · rcases m.htr 1 2 3 (by decide) (by decide) with h30 | h30
                · linarith only [h0, h30, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h32 | h32
                  · linarith only [h0, h30, h32, h4, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h34 | h34
                    · linarith only [h0, h30, h34, h4, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h36 | h36
                      · linarith only [h1, h36, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h38 | h38
                        · linarith only [h0, h30, h38, h4, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi4]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h40 | h40
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h41 | h41
                            · linarith only [h0, h36, h4, h41, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi1]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h43 | h43
                              · linarith only [h0, h4, h43, h5, hlam, hphi, u0ehi7, u0elo0]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h45 | h45
                                · rcases h1bigk with h46c | h46c | h46c | h46c | h46c | h46c | h46c | h46c | h46c | h46c | h46c | h46c | h46c | h46c | h46c | h46c | h46c | h46c | h46c | h46c | h46c | h46c | h46c | h46c | h46c
                                  · have p46_0 := h46c.1
                                    have p46_1 := h46c.2.1
                                    have p46_2 := h46c.2.2.1
                                    have p46_3 := h46c.2.2.2
                                    linarith only [hlam, p46_0]
                                  · have p46_0 := h46c.1
                                    have p46_1 := h46c.2.1
                                    have p46_2 := h46c.2.2.1
                                    have p46_3 := h46c.2.2.2
                                    rcases p46_3 (m.d 0 1) (by simp) with h48 | h48
                                    · rcases p46_3 (m.d 1 2) (by simp) with h49 | h49
                                      · linarith only [h49, hlam, p46_0]
                                      · rcases p46_3 (m.d 1 3) (by simp) with h51 | h51
                                        · linarith only [h1, h51, hlam]
                                        · linarith only [h30, h51, hlam]
                                    · linarith only [h48, hlam, p46_0]
                                  · have p46_0 := h46c.1
                                    have p46_1 := h46c.2.1
                                    have p46_2 := h46c.2.2.1
                                    have p46_3 := h46c.2.2.2
                                    linarith only [hlam, hphi, ht0b, ht34, ht45, ht5b, p46_1, u0elo0, u3ehi1]
                                  · have p46_0 := h46c.1
                                    have p46_1 := h46c.2.1
                                    have p46_2 := h46c.2.2.1
                                    have p46_3 := h46c.2.2.2
                                    linarith only [h40, hc45, hlam, hphi, ht0b, ht5b, p46_1, u0elo0]
                                  · have p46_0 := h46c.1
                                    have p46_1 := h46c.2.1
                                    have p46_2 := h46c.2.2.1
                                    have p46_3 := h46c.2.2.2
                                    linarith only [h38, hlam, hphi, ht0b, ht34, ht45, ht5b, p46_1, u0elo0, u3ehi1]
                                  · have p46_0 := h46c.1
                                    have p46_1 := h46c.2.1
                                    have p46_2 := h46c.2.2.1
                                    have p46_3 := h46c.2.2.2
                                    linarith only [h0, hlam, p46_0]
                                  · have p46_0 := h46c.1
                                    have p46_1 := h46c.2.1
                                    have p46_2 := h46c.2.2.1
                                    have p46_3 := h46c.2.2.2
                                    linarith only [hlam, p46_0]
                                  · have p46_0 := h46c.1
                                    have p46_1 := h46c.2.1
                                    have p46_2 := h46c.2.2.1
                                    have p46_3 := h46c.2.2.2
                                    linarith only [h30, hlam, p46_0]
                                  · have p46_0 := h46c.1
                                    have p46_1 := h46c.2.1
                                    have p46_2 := h46c.2.2.1
                                    have p46_3 := h46c.2.2.2
                                    linarith only [h32, hlam, p46_0]
                                  · have p46_0 := h46c.1
                                    have p46_1 := h46c.2.1
                                    have p46_2 := h46c.2.2.1
                                    have p46_3 := h46c.2.2.2
                                    linarith only [h34, hlam, p46_0]
                                  · have p46_0 := h46c.1
                                    have p46_1 := h46c.2.1
                                    have p46_2 := h46c.2.2.1
                                    have p46_3 := h46c.2.2.2
                                    linarith only [h1, hlam, p46_0]
                                  · have p46_0 := h46c.1
                                    have p46_1 := h46c.2.1
                                    have p46_2 := h46c.2.2.1
                                    have p46_3 := h46c.2.2.2
                                    linarith only [h1, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p46_1, u0elo0]
                                  · have p46_0 := h46c.1
                                    have p46_1 := h46c.2.1
                                    have p46_2 := h46c.2.2.1
                                    have p46_3 := h46c.2.2.2
                                    linarith only [hlam, p46_0]
                                  · have p46_0 := h46c.1
                                    have p46_1 := h46c.2.1
                                    have p46_2 := h46c.2.2.1
                                    have p46_3 := h46c.2.2.2
                                    linarith only [h36, hlam, p46_1]
                                  · have p46_0 := h46c.1
                                    have p46_1 := h46c.2.1
                                    have p46_2 := h46c.2.2.1
                                    have p46_3 := h46c.2.2.2
                                    linarith only [h38, hlam, p46_1]
                                  · have p46_0 := h46c.1
                                    have p46_1 := h46c.2.1
                                    have p46_2 := h46c.2.2.1
                                    have p46_3 := h46c.2.2.2
                                    linarith only [h2, hlam, p46_0]
                                  · have p46_0 := h46c.1
                                    have p46_1 := h46c.2.1
                                    have p46_2 := h46c.2.2.1
                                    have p46_3 := h46c.2.2.2
                                    linarith only [h2, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p46_1, u0elo0]
                                  · have p46_0 := h46c.1
                                    have p46_1 := h46c.2.1
                                    have p46_2 := h46c.2.2.1
                                    have p46_3 := h46c.2.2.2
                                    linarith only [h2, hlam, hphi, ht0b, ht34, ht45, ht5b, p46_1, u0elo0, u3ehi1]
                                  · have p46_0 := h46c.1
                                    have p46_1 := h46c.2.1
                                    have p46_2 := h46c.2.2.1
                                    have p46_3 := h46c.2.2.2
                                    linarith only [hlam, p46_0]
                                  · have p46_0 := h46c.1
                                    have p46_1 := h46c.2.1
                                    have p46_2 := h46c.2.2.1
                                    have p46_3 := h46c.2.2.2
                                    linarith only [h2, h38, hlam, hphi, ht0b, ht34, ht45, ht5b, p46_1, u0elo0, u3ehi1]
                                  · have p46_0 := h46c.1
                                    have p46_1 := h46c.2.1
                                    have p46_2 := h46c.2.2.1
                                    have p46_3 := h46c.2.2.2
                                    linarith only [h3, hlam, p46_0]
                                  · have p46_0 := h46c.1
                                    have p46_1 := h46c.2.1
                                    have p46_2 := h46c.2.2.1
                                    have p46_3 := h46c.2.2.2
                                    linarith only [h3, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p46_1, u0elo0]
                                  · have p46_0 := h46c.1
                                    have p46_1 := h46c.2.1
                                    have p46_2 := h46c.2.2.1
                                    have p46_3 := h46c.2.2.2
                                    linarith only [h3, hlam, hphi, ht0b, ht34, ht45, ht5b, p46_1, u0elo0, u3ehi1]
                                  · have p46_0 := h46c.1
                                    have p46_1 := h46c.2.1
                                    have p46_2 := h46c.2.2.1
                                    have p46_3 := h46c.2.2.2
                                    linarith only [h40, hlam, p46_0]
                                  · have p46_0 := h46c.1
                                    have p46_1 := h46c.2.1
                                    have p46_2 := h46c.2.2.1
                                    have p46_3 := h46c.2.2.2
                                    linarith only [hlam, p46_0]
                                · linarith only [h29, h45, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3, u3ehi3]
                          · linarith only [h2, h29, h36, h40, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi1]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h80 | h80
                · linarith only [h0, h80, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h82 | h82
                  · linarith only [h0, h4, h80, h82, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h84 | h84
                    · linarith only [h0, h4, h80, h84, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h86 | h86
                      · linarith only [h1, h86, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h88 | h88
                        · linarith only [h0, h4, h5, h80, h88, hlam, hphi, u0ehi7, u0elo0]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h90 | h90
                          · linarith only [h29, h90, hc14, hlam, hphi, ht01, u0ehi8]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h92 | h92
                            · linarith only [h0, h4, h86, h92, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi1]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h94 | h94
                              · linarith only [h0, h4, h5, h94, hlam, hphi, u0ehi7, u0elo0]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h96 | h96
                                · linarith only [h29, h96, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi8]
                                · linarith only [h86, h96, hc45, hlam, hphi, ht34, u3ehi1]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h99 | h99
            · rcases m.htr 0 4 5 (by decide) (by decide) with h100 | h100
              · rcases m.htr 1 2 3 (by decide) (by decide) with h101 | h101
                · linarith only [h0, h101, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h103 | h103
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h104 | h104
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h105 | h105
                      · linarith only [h1, h105, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                      · linarith only [h101, h103, h105, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h108 | h108
                      · linarith only [h1, h108, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                      · linarith only [h101, h103, h108, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h111 | h111
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h112 | h112
                      · linarith only [h1, h112, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h114 | h114
                        · linarith only [h112, h114, h2, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi4]
                        · linarith only [h114, h99, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi1]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h117 | h117
                      · linarith only [h1, h117, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h119 | h119
                        · linarith only [h117, h119, h2, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi4]
                        · linarith only [h1, h119, h99, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi1]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h122 | h122
                · linarith only [h122, h4, hc12, hlam, hphi, ht01, u0ehi6]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h124 | h124
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h125 | h125
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h126 | h126
                      · linarith only [h1, h126, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                      · linarith only [h122, h124, h126, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h129 | h129
                      · linarith only [h1, h129, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                      · linarith only [h122, h124, h129, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h132 | h132
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h133 | h133
                      · linarith only [h1, h133, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h135 | h135
                        · linarith only [h133, h135, h2, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi4]
                        · linarith only [h1, h135, h99, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi1]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h138 | h138
                      · linarith only [h1, h138, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h140 | h140
                        · linarith only [h138, h140, h2, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi4]
                        · linarith only [h1, h140, h99, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi1]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h143 | h143
              · rcases m.htr 1 2 3 (by decide) (by decide) with h144 | h144
                · linarith only [h144, h4, hc12, hlam, hphi, ht01, u0ehi6]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h146 | h146
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h147 | h147
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h148 | h148
                      · linarith only [h1, h148, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                      · linarith only [h144, h146, h148, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h151 | h151
                      · linarith only [h1, h151, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                      · linarith only [h144, h146, h151, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h154 | h154
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h155 | h155
                      · linarith only [h1, h155, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h157 | h157
                        · linarith only [h155, h157, h2, h99, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi0]
                        · linarith only [h144, h154, h157, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h160 | h160
                      · linarith only [h1, h160, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h162 | h162
                        · linarith only [h160, h162, h2, h4, h99, hlam, hphi, u0ehi6, u0elo0]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h164 | h164
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h165 | h165
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h166 | h166
                              · linarith only [h166, h4, h99, hc23, hlam, hphi, ht01, ht12, u0ehi6]
                              · linarith only [h166, h4, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi6]
                            · linarith only [h165, h4, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi6]
                          · linarith only [h143, h160, h164, h2, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi1]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h171 | h171
                · linarith only [h171, h4, hc12, hlam, hphi, ht01, u0ehi6]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h173 | h173
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h174 | h174
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h175 | h175
                      · linarith only [h1, h175, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                      · linarith only [h171, h173, h175, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h178 | h178
                      · linarith only [h1, h178, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                      · linarith only [h171, h173, h178, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h181 | h181
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h182 | h182
                      · linarith only [h1, h182, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h184 | h184
                        · linarith only [h182, h184, h2, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi4]
                        · linarith only [h171, h181, h184, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h187 | h187
                      · linarith only [h1, h187, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h189 | h189
                        · linarith only [h187, h189, h2, h4, h99, hlam, hphi, u0ehi6, u0elo0]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h191 | h191
                          · linarith only [h143, h191, h2, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h193 | h193
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h194 | h194
                              · linarith only [h194, h4, h99, hc23, hlam, hphi, ht01, ht12, u0ehi6]
                              · linarith only [h194, h4, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi6]
                            · linarith only [h193, h4, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi6]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h198 | h198
          · rcases m.htr 0 3 5 (by decide) (by decide) with h199 | h199
            · linarith only [h0, h198, h199, h3, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h201 | h201
              · linarith only [h2, h201, h3, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h203 | h203
                · linarith only [h0, h203, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h205 | h205
                  · linarith only [h0, h198, h203, h205, h3, hc15, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h207 | h207
                    · linarith only [h0, h198, h203, h207, h3, hc15, hc25, hlam, hphi, ht01, ht0b, ht5b]
                    · linarith only [h0, h198, h203, h207, h3, hc12, hc25, hlam, hphi]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h210 | h210
            · linarith only [h1, h210, h3, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h212 | h212
              · linarith only [h2, h212, h3, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h214 | h214
                · linarith only [h198, h214, hc12, hlam, hphi, ht01, u0ehi6]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h216 | h216
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h217 | h217
                    · linarith only [h1, h214, h217, h3, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h219 | h219
                      · linarith only [h1, h217, h219, h3, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                      · linarith only [h214, h216, h219, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h222 | h222
                    · linarith only [h216, h222, h3, hc24, hlam, hphi, ht01, ht12, u0ehi5]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h224 | h224
                      · linarith only [h1, h222, h224, h3, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h226 | h226
                        · linarith only [h2, h210, h222, h224, h226, h3, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi0]
                        · linarith only [h2, h224, h226, h3, hc35, hlam, hphi, u3ehi1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h229 | h229
        · rcases m.htr 0 2 3 (by decide) (by decide) with h230 | h230
          · rcases m.htr 0 3 5 (by decide) (by decide) with h231 | h231
            · rcases m.htr 0 4 5 (by decide) (by decide) with h232 | h232
              · rcases m.htr 1 2 3 (by decide) (by decide) with h233 | h233
                · linarith only [h0, h233, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h235 | h235
                  · linarith only [h0, h2, h230, h233, h235, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                  · linarith only [h0, h2, h230, h233, h235, hc12, hc24, hlam, hphi]
              · linarith only [h0, h2, h230, h232, hc45, hlam, hphi, ht34, u3ehi2]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h239 | h239
              · rcases m.htr 1 2 3 (by decide) (by decide) with h240 | h240
                · linarith only [h0, h240, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h242 | h242
                  · linarith only [h230, h240, h242, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                  · linarith only [h0, h2, h230, h240, h242, hc12, hc24, hlam, hphi]
              · linarith only [h0, h2, h230, h239, hc45, hlam, hphi, ht34, u3ehi2]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h246 | h246
            · rcases m.htr 0 4 5 (by decide) (by decide) with h247 | h247
              · rcases m.htr 1 2 3 (by decide) (by decide) with h248 | h248
                · linarith only [h230, h248, hc12, hlam, hphi, ht01, u0ehi6]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h250 | h250
                  · linarith only [h1, h2, h248, h250, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h252 | h252
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h253 | h253
                      · linarith only [h1, h253, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                      · linarith only [h1, h2, h253, hc34, hlam, hphi, u3ehi1]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h256 | h256
                      · linarith only [h1, h2, h250, h256, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                      · linarith only [h1, h2, h256, hc34, hlam, hphi, u3ehi1]
              · linarith only [h1, h2, h246, h247, hc45, hlam, hphi, ht34, u3ehi4]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h260 | h260
              · rcases m.htr 1 2 3 (by decide) (by decide) with h261 | h261
                · linarith only [h0, h261, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h263 | h263
                  · linarith only [h1, h2, h261, h263, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h265 | h265
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h266 | h266
                      · linarith only [h1, h2, h263, h266, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                      · linarith only [h1, h2, h266, hc34, hlam, hphi, u3ehi1]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h269 | h269
                      · linarith only [h1, h269, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                      · linarith only [h1, h2, h269, hc34, hlam, hphi, u3ehi1]
              · linarith only [h1, h2, h260, hc45, hlam, hphi, ht34, u3ehi1]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h273 | h273
          · rcases m.htr 0 3 5 (by decide) (by decide) with h274 | h274
            · linarith only [h0, h229, h273, h274, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h276 | h276
              · rcases m.htr 1 2 3 (by decide) (by decide) with h277 | h277
                · linarith only [h0, h229, h276, h277, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3, u3ehi2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h279 | h279
                  · linarith only [h0, h229, h273, h276, h277, h279, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                  · linarith only [h0, h2, h273, h277, h279, hc12, hc24, hlam, hphi]
              · linarith only [h0, h2, h273, h276, hc45, hlam, hphi, ht34, u3ehi2]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h283 | h283
            · linarith only [h1, h229, h283, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h285 | h285
              · rcases m.htr 1 2 3 (by decide) (by decide) with h286 | h286
                · linarith only [h273, h286, hc12, hlam, hphi, ht01, u0ehi6]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h288 | h288
                  · linarith only [h1, h2, h286, h288, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h290 | h290
                    · linarith only [h1, h229, h286, h290, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h292 | h292
                      · linarith only [h1, h2, h288, h292, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                      · linarith only [h1, h2, h292, hc34, hlam, hphi, u3ehi1]
              · linarith only [h1, h2, h285, hc45, hlam, hphi, ht34, u3ehi1]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h296 | h296
      · rcases m.htr 0 1 5 (by decide) (by decide) with h297 | h297
        · rcases m.htr 0 2 3 (by decide) (by decide) with h298 | h298
          · linarith only [h0, h1, h298, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h300 | h300
            · rcases m.htr 0 4 5 (by decide) (by decide) with h301 | h301
              · rcases m.htr 1 2 3 (by decide) (by decide) with h302 | h302
                · linarith only [h298, h302, hc12, hlam, hphi, ht01, u0ehi6]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h304 | h304
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h305 | h305
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h306 | h306
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h307 | h307
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h308 | h308
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h309 | h309
                            · linarith only [h0, h1, h302, h304, h309, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                            · linarith only [h0, h1, h302, h309, hc12, hc34, hlam, hphi, ht23]
                          · linarith only [h296, h301, h306, h308, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                        · linarith only [h1, h307, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi5]
                      · linarith only [h1, h296, h301, h306, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi9]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h315 | h315
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h316 | h316
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h317 | h317
                          · linarith only [h304, h305, h317, hlam]
                          · linarith only [h296, h301, h315, h317, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                        · linarith only [h1, h316, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi5]
                      · linarith only [h1, h297, h304, h305, h315, hc24, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h322 | h322
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h323 | h323
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h324 | h324
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h325 | h325
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h326 | h326
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h327 | h327
                              · linarith only [h296, h304, h322, h327, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi4]
                              · linarith only [h1, h296, h302, h304, h322, h324, h327, hc15, hc25, hlam, hphi, ht01, ht0b, ht5b]
                            · linarith only [h1, h296, h302, h323, h326, hlam]
                          · linarith only [h301, h304, h322, h324, h325, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3, u3ehi4]
                        · linarith only [h1, h296, h304, h324, hc12, hc35, hlam, hphi, ht23]
                      · linarith only [h1, h296, h304, h322, h323, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h334 | h334
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h335 | h335
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h336 | h336
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h337 | h337
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h338 | h338
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h339 | h339
                                · rcases h1bigk with h340c | h340c | h340c | h340c | h340c | h340c | h340c | h340c | h340c | h340c | h340c | h340c | h340c | h340c | h340c | h340c | h340c | h340c | h340c | h340c | h340c | h340c | h340c | h340c | h340c
                                  · have p340_0 := h340c.1
                                    have p340_1 := h340c.2.1
                                    have p340_2 := h340c.2.2.1
                                    have p340_3 := h340c.2.2.2
                                    linarith only [hlam, p340_0]
                                  · have p340_0 := h340c.1
                                    have p340_1 := h340c.2.1
                                    have p340_2 := h340c.2.2.1
                                    have p340_3 := h340c.2.2.2
                                    linarith only [h1, h302, hc12, hc23, hlam, hphi, p340_1]
                                  · have p340_0 := h340c.1
                                    have p340_1 := h340c.2.1
                                    have p340_2 := h340c.2.2.1
                                    have p340_3 := h340c.2.2.2
                                    linarith only [h1, hlam, p340_0]
                                  · have p340_0 := h340c.1
                                    have p340_1 := h340c.2.1
                                    have p340_2 := h340c.2.2.1
                                    have p340_3 := h340c.2.2.2
                                    linarith only [h335, h336, hlam, hphi, ht0b, ht34, ht45, ht5b, p340_1, u0elo0, u3ehi4]
                                  · have p340_0 := h340c.1
                                    have p340_1 := h340c.2.1
                                    have p340_2 := h340c.2.2.1
                                    have p340_3 := h340c.2.2.2
                                    linarith only [h1, h302, h335, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p340_1, u3ehi4]
                                  · have p340_0 := h340c.1
                                    have p340_1 := h340c.2.1
                                    have p340_2 := h340c.2.2.1
                                    have p340_3 := h340c.2.2.2
                                    linarith only [h0, hlam, p340_0]
                                  · have p340_0 := h340c.1
                                    have p340_1 := h340c.2.1
                                    have p340_2 := h340c.2.2.1
                                    have p340_3 := h340c.2.2.2
                                    linarith only [hlam, p340_0]
                                  · have p340_0 := h340c.1
                                    have p340_1 := h340c.2.1
                                    have p340_2 := h340c.2.2.1
                                    have p340_3 := h340c.2.2.2
                                    linarith only [h302, hlam, p340_0]
                                  · have p340_0 := h340c.1
                                    have p340_1 := h340c.2.1
                                    have p340_2 := h340c.2.2.1
                                    have p340_3 := h340c.2.2.2
                                    linarith only [h304, hlam, p340_0]
                                  · have p340_0 := h340c.1
                                    have p340_1 := h340c.2.1
                                    have p340_2 := h340c.2.2.1
                                    have p340_3 := h340c.2.2.2
                                    linarith only [h322, hlam, p340_0]
                                  · have p340_0 := h340c.1
                                    have p340_1 := h340c.2.1
                                    have p340_2 := h340c.2.2.1
                                    have p340_3 := h340c.2.2.2
                                    linarith only [h302, hc23, hlam, hphi, ht01, ht12, p340_1, u0ehi5]
                                  · have p340_0 := h340c.1
                                    have p340_1 := h340c.2.1
                                    have p340_2 := h340c.2.2.1
                                    have p340_3 := h340c.2.2.2
                                    rcases p340_3 (m.d 0 1) (by simp) with h352 | h352
                                    · linarith only [h1, h352, hlam]
                                    · linarith only [h0, h352, hlam]
                                  · have p340_0 := h340c.1
                                    have p340_1 := h340c.2.1
                                    have p340_2 := h340c.2.2.1
                                    have p340_3 := h340c.2.2.2
                                    linarith only [hlam, p340_0]
                                  · have p340_0 := h340c.1
                                    have p340_1 := h340c.2.1
                                    have p340_2 := h340c.2.2.1
                                    have p340_3 := h340c.2.2.2
                                    rcases p340_3 (m.d 0 1) (by simp) with h356 | h356
                                    · linarith only [h1, h356, hlam]
                                    · linarith only [h296, h356, hlam]
                                  · have p340_0 := h340c.1
                                    have p340_1 := h340c.2.1
                                    have p340_2 := h340c.2.2.1
                                    have p340_3 := h340c.2.2.2
                                    rcases p340_3 (m.d 0 1) (by simp) with h359 | h359
                                    · linarith only [h1, h359, hlam]
                                    · linarith only [h297, h359, hlam]
                                  · have p340_0 := h340c.1
                                    have p340_1 := h340c.2.1
                                    have p340_2 := h340c.2.2.1
                                    have p340_3 := h340c.2.2.2
                                    linarith only [h296, hlam, p340_0]
                                  · have p340_0 := h340c.1
                                    have p340_1 := h340c.2.1
                                    have p340_2 := h340c.2.2.1
                                    have p340_3 := h340c.2.2.2
                                    linarith only [h296, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p340_1, u0elo0]
                                  · have p340_0 := h340c.1
                                    have p340_1 := h340c.2.1
                                    have p340_2 := h340c.2.2.1
                                    have p340_3 := h340c.2.2.2
                                    linarith only [h334, hlam, p340_0]
                                  · have p340_0 := h340c.1
                                    have p340_1 := h340c.2.1
                                    have p340_2 := h340c.2.2.1
                                    have p340_3 := h340c.2.2.2
                                    linarith only [hlam, p340_0]
                                  · have p340_0 := h340c.1
                                    have p340_1 := h340c.2.1
                                    have p340_2 := h340c.2.2.1
                                    have p340_3 := h340c.2.2.2
                                    linarith only [h1, h296, h302, hc15, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p340_1]
                                  · have p340_0 := h340c.1
                                    have p340_1 := h340c.2.1
                                    have p340_2 := h340c.2.2.1
                                    have p340_3 := h340c.2.2.2
                                    linarith only [h297, hlam, p340_0]
                                  · have p340_0 := h340c.1
                                    have p340_1 := h340c.2.1
                                    have p340_2 := h340c.2.2.1
                                    have p340_3 := h340c.2.2.2
                                    linarith only [h1, h297, h302, hc12, hc23, hlam, hphi, p340_1]
                                  · have p340_0 := h340c.1
                                    have p340_1 := h340c.2.1
                                    have p340_2 := h340c.2.2.1
                                    have p340_3 := h340c.2.2.2
                                    linarith only [h335, hlam, p340_0]
                                  · have p340_0 := h340c.1
                                    have p340_1 := h340c.2.1
                                    have p340_2 := h340c.2.2.1
                                    have p340_3 := h340c.2.2.2
                                    linarith only [h336, hlam, p340_0]
                                  · have p340_0 := h340c.1
                                    have p340_1 := h340c.2.1
                                    have p340_2 := h340c.2.2.1
                                    have p340_3 := h340c.2.2.2
                                    linarith only [hlam, p340_0]
                                · linarith only [h301, h339, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3, u3ehi3]
                              · linarith only [h1, h296, h302, h336, h338, hc35, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                            · linarith only [h1, h296, h302, h335, h336, h337, hc34, hlam, hphi, u3ehi4]
                          · linarith only [h296, h301, h334, h336, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                        · linarith only [h1, h335, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi5]
                      · linarith only [h1, h296, h301, h334, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi9]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h378 | h378
                · linarith only [h0, h378, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h380 | h380
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h381 | h381
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h382 | h382
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h383 | h383
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h384 | h384
                          · linarith only [h0, h1, h301, h378, h380, h384, hc23, hlam, hphi, ht01, ht12, u0ehi8]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h386 | h386
                            · linarith only [h0, h1, h378, h380, h386, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                            · linarith only [h0, h1, h378, h386, hc12, hc34, hlam, hphi, ht23]
                        · linarith only [h0, h1, h380, h382, h383, hc35, hlam, hphi, u3ehi3]
                      · linarith only [h0, h1, h382, hc12, hc34, hlam, hphi, ht23]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h391 | h391
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h392 | h392
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h393 | h393
                          · linarith only [h297, h301, h380, h381, h393, hlam, hphi, u0ehi8, u0elo0]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h395 | h395
                            · linarith only [h1, h297, h378, h380, h381, h395, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                            · linarith only [h1, h297, h378, h381, h395, hc12, hc34, hlam, hphi, ht23]
                        · linarith only [h1, h297, h380, h381, h391, h392, hc35, hlam, hphi, u3ehi3]
                      · linarith only [h1, h297, h381, h391, hc12, hc34, hlam, hphi, ht23]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h400 | h400
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h401 | h401
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h402 | h402
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h403 | h403
                          · linarith only [h296, h301, h403, hlam, hphi, u0ehi8, u0elo0]
                          · linarith only [h380, h400, h403, hlam]
                        · linarith only [h1, h402, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi5]
                      · linarith only [h1, h296, h380, h400, h401, hc25, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h408 | h408
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h409 | h409
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h410 | h410
                          · linarith only [h296, h301, h410, hlam, hphi, u0ehi8, u0elo0]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h412 | h412
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h413 | h413
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h414 | h414
                                · linarith only [h301, h414, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi8]
                                · rcases h1bigk with h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c | h416c
                                  · have p416_0 := h416c.1
                                    have p416_1 := h416c.2.1
                                    have p416_2 := h416c.2.2.1
                                    have p416_3 := h416c.2.2.2
                                    linarith only [hlam, p416_0]
                                  · have p416_0 := h416c.1
                                    have p416_1 := h416c.2.1
                                    have p416_2 := h416c.2.2.1
                                    have p416_3 := h416c.2.2.2
                                    linarith only [h1, h378, hc12, hc23, hlam, hphi, p416_1]
                                  · have p416_0 := h416c.1
                                    have p416_1 := h416c.2.1
                                    have p416_2 := h416c.2.2.1
                                    have p416_3 := h416c.2.2.2
                                    linarith only [h1, hlam, p416_0]
                                  · have p416_0 := h416c.1
                                    have p416_1 := h416c.2.1
                                    have p416_2 := h416c.2.2.1
                                    have p416_3 := h416c.2.2.2
                                    linarith only [h1, h378, h408, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p416_1, u3ehi3]
                                  · have p416_0 := h416c.1
                                    have p416_1 := h416c.2.1
                                    have p416_2 := h416c.2.2.1
                                    have p416_3 := h416c.2.2.2
                                    linarith only [h1, h378, h409, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p416_1, u3ehi4]
                                  · have p416_0 := h416c.1
                                    have p416_1 := h416c.2.1
                                    have p416_2 := h416c.2.2.1
                                    have p416_3 := h416c.2.2.2
                                    linarith only [h0, hlam, p416_0]
                                  · have p416_0 := h416c.1
                                    have p416_1 := h416c.2.1
                                    have p416_2 := h416c.2.2.1
                                    have p416_3 := h416c.2.2.2
                                    linarith only [hlam, p416_0]
                                  · have p416_0 := h416c.1
                                    have p416_1 := h416c.2.1
                                    have p416_2 := h416c.2.2.1
                                    have p416_3 := h416c.2.2.2
                                    linarith only [h378, hlam, p416_0]
                                  · have p416_0 := h416c.1
                                    have p416_1 := h416c.2.1
                                    have p416_2 := h416c.2.2.1
                                    have p416_3 := h416c.2.2.2
                                    linarith only [h380, hlam, p416_0]
                                  · have p416_0 := h416c.1
                                    have p416_1 := h416c.2.1
                                    have p416_2 := h416c.2.2.1
                                    have p416_3 := h416c.2.2.2
                                    linarith only [h400, hlam, p416_0]
                                  · have p416_0 := h416c.1
                                    have p416_1 := h416c.2.1
                                    have p416_2 := h416c.2.2.1
                                    have p416_3 := h416c.2.2.2
                                    linarith only [h378, hc23, hlam, hphi, ht01, ht12, p416_1, u0ehi5]
                                  · have p416_0 := h416c.1
                                    have p416_1 := h416c.2.1
                                    have p416_2 := h416c.2.2.1
                                    have p416_3 := h416c.2.2.2
                                    rcases p416_3 (m.d 0 1) (by simp) with h428 | h428
                                    · linarith only [h1, h428, hlam]
                                    · linarith only [h0, h428, hlam]
                                  · have p416_0 := h416c.1
                                    have p416_1 := h416c.2.1
                                    have p416_2 := h416c.2.2.1
                                    have p416_3 := h416c.2.2.2
                                    linarith only [hlam, p416_0]
                                  · have p416_0 := h416c.1
                                    have p416_1 := h416c.2.1
                                    have p416_2 := h416c.2.2.1
                                    have p416_3 := h416c.2.2.2
                                    rcases p416_3 (m.d 0 1) (by simp) with h432 | h432
                                    · linarith only [h1, h432, hlam]
                                    · linarith only [h296, h432, hlam]
                                  · have p416_0 := h416c.1
                                    have p416_1 := h416c.2.1
                                    have p416_2 := h416c.2.2.1
                                    have p416_3 := h416c.2.2.2
                                    rcases p416_3 (m.d 0 1) (by simp) with h435 | h435
                                    · linarith only [h1, h435, hlam]
                                    · linarith only [h297, h435, hlam]
                                  · have p416_0 := h416c.1
                                    have p416_1 := h416c.2.1
                                    have p416_2 := h416c.2.2.1
                                    have p416_3 := h416c.2.2.2
                                    linarith only [h296, hlam, p416_0]
                                  · have p416_0 := h416c.1
                                    have p416_1 := h416c.2.1
                                    have p416_2 := h416c.2.2.1
                                    have p416_3 := h416c.2.2.2
                                    linarith only [h297, h410, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p416_1, u0elo0]
                                  · have p416_0 := h416c.1
                                    have p416_1 := h416c.2.1
                                    have p416_2 := h416c.2.2.1
                                    have p416_3 := h416c.2.2.2
                                    linarith only [h408, hlam, p416_0]
                                  · have p416_0 := h416c.1
                                    have p416_1 := h416c.2.1
                                    have p416_2 := h416c.2.2.1
                                    have p416_3 := h416c.2.2.2
                                    linarith only [hlam, p416_0]
                                  · have p416_0 := h416c.1
                                    have p416_1 := h416c.2.1
                                    have p416_2 := h416c.2.2.1
                                    have p416_3 := h416c.2.2.2
                                    linarith only [h410, hlam, p416_1]
                                  · have p416_0 := h416c.1
                                    have p416_1 := h416c.2.1
                                    have p416_2 := h416c.2.2.1
                                    have p416_3 := h416c.2.2.2
                                    linarith only [h297, hlam, p416_0]
                                  · have p416_0 := h416c.1
                                    have p416_1 := h416c.2.1
                                    have p416_2 := h416c.2.2.1
                                    have p416_3 := h416c.2.2.2
                                    linarith only [h1, h297, h378, hc12, hc23, hlam, hphi, p416_1]
                                  · have p416_0 := h416c.1
                                    have p416_1 := h416c.2.1
                                    have p416_2 := h416c.2.2.1
                                    have p416_3 := h416c.2.2.2
                                    linarith only [h409, hlam, p416_0]
                                  · have p416_0 := h416c.1
                                    have p416_1 := h416c.2.1
                                    have p416_2 := h416c.2.2.1
                                    have p416_3 := h416c.2.2.2
                                    linarith only [h1, h297, h378, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p416_1]
                                  · have p416_0 := h416c.1
                                    have p416_1 := h416c.2.1
                                    have p416_2 := h416c.2.2.1
                                    have p416_3 := h416c.2.2.2
                                    linarith only [hlam, p416_0]
                              · linarith only [h1, h297, h378, h409, h413, hlam]
                            · linarith only [h1, h297, h378, h408, h410, h412, hlam]
                        · linarith only [h1, h409, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi5]
                      · linarith only [h1, h297, h301, h408, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi8]
            · linarith only [h1, h297, h300, hlam]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h453 | h453
          · linarith only [h0, h1, h453, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h455 | h455
            · rcases m.htr 0 4 5 (by decide) (by decide) with h456 | h456
              · linarith only [h296, h297, h456, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h458 | h458
                · linarith only [h453, h458, hc12, hlam, hphi, ht01, u0ehi6]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h460 | h460
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h461 | h461
                    · linarith only [h0, h297, h461, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h463 | h463
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h464 | h464
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h465 | h465
                          · linarith only [h0, h456, h460, h465, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                          · linarith only [h0, h297, h460, h463, h465, hc45, hlam, hphi, ht34, u3ehi3]
                        · linarith only [h455, h464, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi1]
                      · linarith only [h0, h1, h463, hc12, hc34, hlam, hphi, ht23]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h470 | h470
                    · linarith only [h296, h297, h460, h470, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h472 | h472
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h473 | h473
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h474 | h474
                          · linarith only [h296, h456, h474, hlam, hphi, u0ehi8, u0elo0]
                          · linarith only [h296, h297, h472, h474, hc45, hlam, hphi, ht34, u3ehi3]
                        · linarith only [h455, h473, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi1]
                      · linarith only [h1, h296, h460, h472, hc12, hc34, hlam, hphi, ht23]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h479 | h479
              · linarith only [h296, h297, h479, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h481 | h481
                · linarith only [h0, h481, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h483 | h483
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h484 | h484
                    · linarith only [h0, h297, h484, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h486 | h486
                      · linarith only [h0, h1, h455, h483, h486, hc35, hlam, hphi, u3ehi3]
                      · linarith only [h0, h1, h486, hc12, hc34, hlam, hphi, ht23]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h489 | h489
                    · linarith only [h296, h297, h483, h489, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h491 | h491
                      · linarith only [h1, h296, h455, h491, hc35, hlam, hphi, u3ehi3]
                      · linarith only [h1, h296, h483, h491, hc12, hc34, hlam, hphi, ht23]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h494 | h494
        · rcases m.htr 0 2 3 (by decide) (by decide) with h495 | h495
          · linarith only [h0, h1, h495, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h497 | h497
            · rcases m.htr 0 4 5 (by decide) (by decide) with h498 | h498
              · rcases m.htr 1 2 3 (by decide) (by decide) with h499 | h499
                · linarith only [h495, h499, hc12, hlam, hphi, ht01, u0ehi6]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h501 | h501
                  · linarith only [h0, h296, h501, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h503 | h503
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h504 | h504
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h505 | h505
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h506 | h506
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h507 | h507
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h508 | h508
                              · linarith only [h0, h503, h508, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi4]
                              · linarith only [h0, h296, h499, h504, h508, hc12, hc35, hlam, hphi, ht23]
                            · linarith only [h499, h504, h507, hlam]
                          · linarith only [h0, h296, h503, h505, h506, hc45, hlam, hphi, ht34, u3ehi4]
                        · linarith only [h0, h296, h504, h505, hc12, hc35, hlam, hphi, ht23]
                      · linarith only [h1, h494, h504, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi9]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h515 | h515
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h516 | h516
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h517 | h517
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h518 | h518
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h519 | h519
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h520 | h520
                                · rcases h1bigk with h521c | h521c | h521c | h521c | h521c | h521c | h521c | h521c | h521c | h521c | h521c | h521c | h521c | h521c | h521c | h521c | h521c | h521c | h521c | h521c | h521c | h521c | h521c | h521c | h521c
                                  · have p521_0 := h521c.1
                                    have p521_1 := h521c.2.1
                                    have p521_2 := h521c.2.2.1
                                    have p521_3 := h521c.2.2.2
                                    linarith only [hlam, p521_0]
                                  · have p521_0 := h521c.1
                                    have p521_1 := h521c.2.1
                                    have p521_2 := h521c.2.2.1
                                    have p521_3 := h521c.2.2.2
                                    linarith only [h296, h499, h515, hc12, hc23, hlam, hphi, p521_1]
                                  · have p521_0 := h521c.1
                                    have p521_1 := h521c.2.1
                                    have p521_2 := h521c.2.2.1
                                    have p521_3 := h521c.2.2.2
                                    linarith only [h1, hlam, p521_0]
                                  · have p521_0 := h521c.1
                                    have p521_1 := h521c.2.1
                                    have p521_2 := h521c.2.2.1
                                    have p521_3 := h521c.2.2.2
                                    linarith only [h296, hlam, p521_0]
                                  · have p521_0 := h521c.1
                                    have p521_1 := h521c.2.1
                                    have p521_2 := h521c.2.2.1
                                    have p521_3 := h521c.2.2.2
                                    linarith only [h516, hlam, hphi, ht0b, ht34, ht45, ht5b, p521_1, u0elo0, u3ehi4]
                                  · have p521_0 := h521c.1
                                    have p521_1 := h521c.2.1
                                    have p521_2 := h521c.2.2.1
                                    have p521_3 := h521c.2.2.2
                                    linarith only [h0, hlam, p521_0]
                                  · have p521_0 := h521c.1
                                    have p521_1 := h521c.2.1
                                    have p521_2 := h521c.2.2.1
                                    have p521_3 := h521c.2.2.2
                                    linarith only [hlam, p521_0]
                                  · have p521_0 := h521c.1
                                    have p521_1 := h521c.2.1
                                    have p521_2 := h521c.2.2.1
                                    have p521_3 := h521c.2.2.2
                                    linarith only [h499, hlam, p521_0]
                                  · have p521_0 := h521c.1
                                    have p521_1 := h521c.2.1
                                    have p521_2 := h521c.2.2.1
                                    have p521_3 := h521c.2.2.2
                                    linarith only [h501, hlam, p521_0]
                                  · have p521_0 := h521c.1
                                    have p521_1 := h521c.2.1
                                    have p521_2 := h521c.2.2.1
                                    have p521_3 := h521c.2.2.2
                                    linarith only [h503, hlam, p521_0]
                                  · have p521_0 := h521c.1
                                    have p521_1 := h521c.2.1
                                    have p521_2 := h521c.2.2.1
                                    have p521_3 := h521c.2.2.2
                                    linarith only [h499, hc23, hlam, hphi, ht01, ht12, p521_1, u0ehi5]
                                  · have p521_0 := h521c.1
                                    have p521_1 := h521c.2.1
                                    have p521_2 := h521c.2.2.1
                                    have p521_3 := h521c.2.2.2
                                    rcases p521_3 (m.d 0 1) (by simp) with h533 | h533
                                    · linarith only [h1, h533, hlam]
                                    · linarith only [h0, h533, hlam]
                                  · have p521_0 := h521c.1
                                    have p521_1 := h521c.2.1
                                    have p521_2 := h521c.2.2.1
                                    have p521_3 := h521c.2.2.2
                                    linarith only [hlam, p521_0]
                                  · have p521_0 := h521c.1
                                    have p521_1 := h521c.2.1
                                    have p521_2 := h521c.2.2.1
                                    have p521_3 := h521c.2.2.2
                                    linarith only [h296, h494, h499, h516, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p521_1, u3ehi4]
                                  · have p521_0 := h521c.1
                                    have p521_1 := h521c.2.1
                                    have p521_2 := h521c.2.2.1
                                    have p521_3 := h521c.2.2.2
                                    rcases p521_3 (m.d 0 1) (by simp) with h538 | h538
                                    · linarith only [h1, h538, hlam]
                                    · linarith only [h494, h538, hlam]
                                  · have p521_0 := h521c.1
                                    have p521_1 := h521c.2.1
                                    have p521_2 := h521c.2.2.1
                                    have p521_3 := h521c.2.2.2
                                    linarith only [h494, h516, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p521_1, u3ehi4]
                                  · have p521_0 := h521c.1
                                    have p521_1 := h521c.2.1
                                    have p521_2 := h521c.2.2.1
                                    have p521_3 := h521c.2.2.2
                                    rcases p521_3 (m.d 0 1) (by simp) with h542 | h542
                                    · linarith only [h296, h542, hlam]
                                    · linarith only [h0, h542, hlam]
                                  · have p521_0 := h521c.1
                                    have p521_1 := h521c.2.1
                                    have p521_2 := h521c.2.2.1
                                    have p521_3 := h521c.2.2.2
                                    linarith only [h515, hlam, p521_0]
                                  · have p521_0 := h521c.1
                                    have p521_1 := h521c.2.1
                                    have p521_2 := h521c.2.2.1
                                    have p521_3 := h521c.2.2.2
                                    linarith only [hlam, p521_0]
                                  · have p521_0 := h521c.1
                                    have p521_1 := h521c.2.1
                                    have p521_2 := h521c.2.2.1
                                    have p521_3 := h521c.2.2.2
                                    rcases p521_3 (m.d 0 1) (by simp) with h547 | h547
                                    · linarith only [h296, h547, hlam]
                                    · linarith only [h494, h547, hlam]
                                  · have p521_0 := h521c.1
                                    have p521_1 := h521c.2.1
                                    have p521_2 := h521c.2.2.1
                                    have p521_3 := h521c.2.2.2
                                    linarith only [h494, hlam, p521_0]
                                  · have p521_0 := h521c.1
                                    have p521_1 := h521c.2.1
                                    have p521_2 := h521c.2.2.1
                                    have p521_3 := h521c.2.2.2
                                    linarith only [h494, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p521_1, u0elo0]
                                  · have p521_0 := h521c.1
                                    have p521_1 := h521c.2.1
                                    have p521_2 := h521c.2.2.1
                                    have p521_3 := h521c.2.2.2
                                    linarith only [h516, hlam, p521_0]
                                  · have p521_0 := h521c.1
                                    have p521_1 := h521c.2.1
                                    have p521_2 := h521c.2.2.1
                                    have p521_3 := h521c.2.2.2
                                    linarith only [h517, hlam, p521_0]
                                  · have p521_0 := h521c.1
                                    have p521_1 := h521c.2.1
                                    have p521_2 := h521c.2.2.1
                                    have p521_3 := h521c.2.2.2
                                    linarith only [hlam, p521_0]
                                · linarith only [h498, h520, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3, u3ehi3]
                              · linarith only [h296, h494, h499, h515, h516, h519, hlam]
                            · linarith only [h296, h494, h499, h515, h516, h518, hc34, hlam, hphi, u3ehi4]
                          · linarith only [h296, h494, h516, h517, hc45, hlam, hphi, ht34, u3ehi4]
                        · linarith only [h296, h515, h516, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi5]
                      · linarith only [h0, h1, h515, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi6]
              · linarith only [h296, h494, h498, hlam]
            · linarith only [h1, h494, h497, hlam]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h563 | h563
          · linarith only [h0, h1, h563, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h565 | h565
            · rcases m.htr 0 4 5 (by decide) (by decide) with h566 | h566
              · rcases m.htr 1 2 3 (by decide) (by decide) with h567 | h567
                · linarith only [h563, h567, hc12, hlam, hphi, ht01, u0ehi6]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h569 | h569
                  · linarith only [h0, h296, h569, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h571 | h571
                    · linarith only [h0, h494, h571, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h573 | h573
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h574 | h574
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h575 | h575
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h576 | h576
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h577 | h577
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h578 | h578
                                · rcases h1bigk with h579c | h579c | h579c | h579c | h579c | h579c | h579c | h579c | h579c | h579c | h579c | h579c | h579c | h579c | h579c | h579c | h579c | h579c | h579c | h579c | h579c | h579c | h579c | h579c | h579c
                                  · have p579_0 := h579c.1
                                    have p579_1 := h579c.2.1
                                    have p579_2 := h579c.2.2.1
                                    have p579_3 := h579c.2.2.2
                                    linarith only [hlam, p579_0]
                                  · have p579_0 := h579c.1
                                    have p579_1 := h579c.2.1
                                    have p579_2 := h579c.2.2.1
                                    have p579_3 := h579c.2.2.2
                                    linarith only [h494, h567, h573, h575, hc12, hc23, hlam, hphi, p579_1]
                                  · have p579_0 := h579c.1
                                    have p579_1 := h579c.2.1
                                    have p579_2 := h579c.2.2.1
                                    have p579_3 := h579c.2.2.2
                                    linarith only [h1, hlam, p579_0]
                                  · have p579_0 := h579c.1
                                    have p579_1 := h579c.2.1
                                    have p579_2 := h579c.2.2.1
                                    have p579_3 := h579c.2.2.2
                                    linarith only [h296, hlam, p579_0]
                                  · have p579_0 := h579c.1
                                    have p579_1 := h579c.2.1
                                    have p579_2 := h579c.2.2.1
                                    have p579_3 := h579c.2.2.2
                                    linarith only [h494, hlam, p579_0]
                                  · have p579_0 := h579c.1
                                    have p579_1 := h579c.2.1
                                    have p579_2 := h579c.2.2.1
                                    have p579_3 := h579c.2.2.2
                                    linarith only [h0, hlam, p579_0]
                                  · have p579_0 := h579c.1
                                    have p579_1 := h579c.2.1
                                    have p579_2 := h579c.2.2.1
                                    have p579_3 := h579c.2.2.2
                                    linarith only [hlam, p579_0]
                                  · have p579_0 := h579c.1
                                    have p579_1 := h579c.2.1
                                    have p579_2 := h579c.2.2.1
                                    have p579_3 := h579c.2.2.2
                                    linarith only [h567, hlam, p579_0]
                                  · have p579_0 := h579c.1
                                    have p579_1 := h579c.2.1
                                    have p579_2 := h579c.2.2.1
                                    have p579_3 := h579c.2.2.2
                                    linarith only [h569, hlam, p579_0]
                                  · have p579_0 := h579c.1
                                    have p579_1 := h579c.2.1
                                    have p579_2 := h579c.2.2.1
                                    have p579_3 := h579c.2.2.2
                                    linarith only [h571, hlam, p579_0]
                                  · have p579_0 := h579c.1
                                    have p579_1 := h579c.2.1
                                    have p579_2 := h579c.2.2.1
                                    have p579_3 := h579c.2.2.2
                                    linarith only [h567, hc23, hlam, hphi, ht01, ht12, p579_1, u0ehi5]
                                  · have p579_0 := h579c.1
                                    have p579_1 := h579c.2.1
                                    have p579_2 := h579c.2.2.1
                                    have p579_3 := h579c.2.2.2
                                    rcases p579_3 (m.d 0 1) (by simp) with h591 | h591
                                    · linarith only [h1, h591, hlam]
                                    · linarith only [h0, h591, hlam]
                                  · have p579_0 := h579c.1
                                    have p579_1 := h579c.2.1
                                    have p579_2 := h579c.2.2.1
                                    have p579_3 := h579c.2.2.2
                                    linarith only [hlam, p579_0]
                                  · have p579_0 := h579c.1
                                    have p579_1 := h579c.2.1
                                    have p579_2 := h579c.2.2.1
                                    have p579_3 := h579c.2.2.2
                                    linarith only [h0, h494, h567, h575, hc23, hlam, hphi, ht01, ht12, p579_1, u0ehi6]
                                  · have p579_0 := h579c.1
                                    have p579_1 := h579c.2.1
                                    have p579_2 := h579c.2.2.1
                                    have p579_3 := h579c.2.2.2
                                    linarith only [h0, h494, h567, hc23, hlam, hphi, ht01, ht12, p579_1, u0ehi6]
                                  · have p579_0 := h579c.1
                                    have p579_1 := h579c.2.1
                                    have p579_2 := h579c.2.2.1
                                    have p579_3 := h579c.2.2.2
                                    linarith only [h0, hc14, hlam, hphi, ht01, p579_1, u0ehi6]
                                  · have p579_0 := h579c.1
                                    have p579_1 := h579c.2.1
                                    have p579_2 := h579c.2.2.1
                                    have p579_3 := h579c.2.2.2
                                    rcases p579_3 (m.d 0 1) (by simp) with h598 | h598
                                    · linarith only [h296, h598, hlam]
                                    · linarith only [h0, h598, hlam]
                                  · have p579_0 := h579c.1
                                    have p579_1 := h579c.2.1
                                    have p579_2 := h579c.2.2.1
                                    have p579_3 := h579c.2.2.2
                                    linarith only [h573, hlam, p579_0]
                                  · have p579_0 := h579c.1
                                    have p579_1 := h579c.2.1
                                    have p579_2 := h579c.2.2.1
                                    have p579_3 := h579c.2.2.2
                                    linarith only [hlam, p579_0]
                                  · have p579_0 := h579c.1
                                    have p579_1 := h579c.2.1
                                    have p579_2 := h579c.2.2.1
                                    have p579_3 := h579c.2.2.2
                                    linarith only [h0, h494, h567, h573, hc23, hlam, hphi, ht01, ht12, p579_1, u0ehi6]
                                  · have p579_0 := h579c.1
                                    have p579_1 := h579c.2.1
                                    have p579_2 := h579c.2.2.1
                                    have p579_3 := h579c.2.2.2
                                    linarith only [h0, hc15, hlam, hphi, ht01, p579_1, u0ehi6]
                                  · have p579_0 := h579c.1
                                    have p579_1 := h579c.2.1
                                    have p579_2 := h579c.2.2.1
                                    have p579_3 := h579c.2.2.2
                                    rcases p579_3 (m.d 0 1) (by simp) with h605 | h605
                                    · linarith only [h494, h605, hlam]
                                    · linarith only [h0, h605, hlam]
                                  · have p579_0 := h579c.1
                                    have p579_1 := h579c.2.1
                                    have p579_2 := h579c.2.2.1
                                    have p579_3 := h579c.2.2.2
                                    linarith only [h574, hlam, p579_0]
                                  · have p579_0 := h579c.1
                                    have p579_1 := h579c.2.1
                                    have p579_2 := h579c.2.2.1
                                    have p579_3 := h579c.2.2.2
                                    linarith only [h575, hlam, p579_0]
                                  · have p579_0 := h579c.1
                                    have p579_1 := h579c.2.1
                                    have p579_2 := h579c.2.2.1
                                    have p579_3 := h579c.2.2.2
                                    linarith only [hlam, p579_0]
                                · linarith only [h566, h578, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3, u3ehi3]
                              · linarith only [h0, h1, h567, h577, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi6]
                            · linarith only [h0, h494, h567, h573, h575, h576, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi6]
                          · linarith only [h0, h296, h566, h575, hlam, hphi, u0ehi6, u0elo3]
                        · linarith only [h565, h574, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi1]
                      · linarith only [h0, h1, h573, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi6]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h617 | h617
                · linarith only [h0, h617, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h619 | h619
                  · linarith only [h0, h296, h566, h619, hc24, hc45, hlam, hphi]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h621 | h621
                    · linarith only [h0, h494, h621, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h623 | h623
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h624 | h624
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h625 | h625
                          · linarith only [h0, h296, h566, h617, h623, h625, hc12, hc23, hlam, hphi]
                          · linarith only [h0, h296, h625, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi6]
                        · linarith only [h565, h624, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi1]
                      · linarith only [h0, h1, h623, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi6]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h630 | h630
              · rcases m.htr 1 2 3 (by decide) (by decide) with h631 | h631
                · linarith only [h0, h631, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h633 | h633
                  · linarith only [h0, h296, h633, hlam]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h635 | h635
                    · linarith only [h0, h494, h635, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h637 | h637
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h638 | h638
                        · linarith only [h0, h1, h565, h631, h638, hc12, hc23, hlam, hphi]
                        · linarith only [h637, h638, hc35, hlam, hphi, u3ehi3]
                      · linarith only [h0, h1, h637, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi6]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h642 | h642
                · linarith only [h0, h642, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h644 | h644
                  · linarith only [h0, h296, h630, h644, hc24, hc45, hlam, hphi]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h646 | h646
                    · linarith only [h0, h494, h646, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h648 | h648
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h649 | h649
                        · linarith only [h565, h642, h649, hc23, hlam, hphi, ht01, ht12, u0ehi7]
                        · linarith only [h648, h649, hc35, hlam, hphi, u3ehi3]
                      · linarith only [h0, h1, h648, hc12, hc34, hlam, hphi, ht23]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h653 | h653
    · rcases m.htr 0 1 4 (by decide) (by decide) with h654 | h654
      · rcases m.htr 0 1 5 (by decide) (by decide) with h655 | h655
        · rcases m.htr 0 2 3 (by decide) (by decide) with h656 | h656
          · rcases m.htr 0 3 5 (by decide) (by decide) with h657 | h657
            · rcases m.htr 0 4 5 (by decide) (by decide) with h658 | h658
              · rcases m.htr 1 2 3 (by decide) (by decide) with h659 | h659
                · rcases m.htr 1 2 4 (by decide) (by decide) with h660 | h660
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h661 | h661
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h662 | h662
                      · linarith only [h653, h662, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h664 | h664
                        · linarith only [h0, h654, h662, h664, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi4]
                        · linarith only [h657, h664, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi1]
                    · linarith only [h0, h661, hc25, hlam, hphi, ht01, ht12, u0ehi5]
                  · linarith only [h0, h653, h659, h660, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                · linarith only [h0, h653, h659, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h670 | h670
                · rcases m.htr 1 2 4 (by decide) (by decide) with h671 | h671
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h672 | h672
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h673 | h673
                      · linarith only [h653, h673, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h675 | h675
                        · linarith only [h0, h654, h673, h675, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi4]
                        · linarith only [h657, h675, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi1]
                    · linarith only [h0, h672, hc25, hlam, hphi, ht01, ht12, u0ehi5]
                  · linarith only [h0, h653, h657, h671, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi4]
                · linarith only [h0, h653, h657, h670, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi4]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h681 | h681
              · rcases m.htr 1 2 3 (by decide) (by decide) with h682 | h682
                · rcases m.htr 1 2 4 (by decide) (by decide) with h683 | h683
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h684 | h684
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h685 | h685
                      · linarith only [h653, h685, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h687 | h687
                        · linarith only [h0, h654, h657, h685, h687, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h689 | h689
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h690 | h690
                            · linarith only [h682, h685, h690, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h692 | h692
                              · linarith only [h0, h654, h657, h682, h687, h689, h692, hc12, hlam, hphi, ht01, u0ehi7]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h694 | h694
                                · rcases h1bigk with h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c | h695c
                                  · have p695_0 := h695c.1
                                    have p695_1 := h695c.2.1
                                    have p695_2 := h695c.2.2.1
                                    have p695_3 := h695c.2.2.2
                                    linarith only [hlam, p695_0]
                                  · have p695_0 := h695c.1
                                    have p695_1 := h695c.2.1
                                    have p695_2 := h695c.2.2.1
                                    have p695_3 := h695c.2.2.2
                                    linarith only [h0, hlam, p695_0]
                                  · have p695_0 := h695c.1
                                    have p695_1 := h695c.2.1
                                    have p695_2 := h695c.2.2.1
                                    have p695_3 := h695c.2.2.2
                                    linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p695_1, u3ehi1]
                                  · have p695_0 := h695c.1
                                    have p695_1 := h695c.2.1
                                    have p695_2 := h695c.2.2.1
                                    have p695_3 := h695c.2.2.2
                                    linarith only [h0, h689, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p695_1]
                                  · have p695_0 := h695c.1
                                    have p695_1 := h695c.2.1
                                    have p695_2 := h695c.2.2.1
                                    have p695_3 := h695c.2.2.2
                                    linarith only [h0, h682, h687, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p695_1, u3ehi2]
                                  · have p695_0 := h695c.1
                                    have p695_1 := h695c.2.1
                                    have p695_2 := h695c.2.2.1
                                    have p695_3 := h695c.2.2.2
                                    linarith only [hc12, hlam, hphi, ht01, p695_1, u0ehi5]
                                  · have p695_0 := h695c.1
                                    have p695_1 := h695c.2.1
                                    have p695_2 := h695c.2.2.1
                                    have p695_3 := h695c.2.2.2
                                    linarith only [hlam, p695_0]
                                  · have p695_0 := h695c.1
                                    have p695_1 := h695c.2.1
                                    have p695_2 := h695c.2.2.1
                                    have p695_3 := h695c.2.2.2
                                    rcases p695_3 (m.d 0 1) (by simp) with h703 | h703
                                    · linarith only [h0, h703, hlam]
                                    · linarith only [h653, h703, hlam]
                                  · have p695_0 := h695c.1
                                    have p695_1 := h695c.2.1
                                    have p695_2 := h695c.2.2.1
                                    have p695_3 := h695c.2.2.2
                                    rcases p695_3 (m.d 0 1) (by simp) with h706 | h706
                                    · linarith only [h0, h706, hlam]
                                    · linarith only [h654, h706, hlam]
                                  · have p695_0 := h695c.1
                                    have p695_1 := h695c.2.1
                                    have p695_2 := h695c.2.2.1
                                    have p695_3 := h695c.2.2.2
                                    rcases p695_3 (m.d 0 1) (by simp) with h709 | h709
                                    · linarith only [h0, h709, hlam]
                                    · linarith only [h655, h709, hlam]
                                  · have p695_0 := h695c.1
                                    have p695_1 := h695c.2.1
                                    have p695_2 := h695c.2.2.1
                                    have p695_3 := h695c.2.2.2
                                    linarith only [h653, hlam, p695_0]
                                  · have p695_0 := h695c.1
                                    have p695_1 := h695c.2.1
                                    have p695_2 := h695c.2.2.1
                                    have p695_3 := h695c.2.2.2
                                    linarith only [h682, hlam, p695_1]
                                  · have p695_0 := h695c.1
                                    have p695_1 := h695c.2.1
                                    have p695_2 := h695c.2.2.1
                                    have p695_3 := h695c.2.2.2
                                    linarith only [hlam, p695_0]
                                  · have p695_0 := h695c.1
                                    have p695_1 := h695c.2.1
                                    have p695_2 := h695c.2.2.1
                                    have p695_3 := h695c.2.2.2
                                    linarith only [h685, hlam, p695_1]
                                  · have p695_0 := h695c.1
                                    have p695_1 := h695c.2.1
                                    have p695_2 := h695c.2.2.1
                                    have p695_3 := h695c.2.2.2
                                    linarith only [h687, hlam, p695_1]
                                  · have p695_0 := h695c.1
                                    have p695_1 := h695c.2.1
                                    have p695_2 := h695c.2.2.1
                                    have p695_3 := h695c.2.2.2
                                    linarith only [h654, hlam, p695_0]
                                  · have p695_0 := h695c.1
                                    have p695_1 := h695c.2.1
                                    have p695_2 := h695c.2.2.1
                                    have p695_3 := h695c.2.2.2
                                    linarith only [h683, hlam, p695_1]
                                  · have p695_0 := h695c.1
                                    have p695_1 := h695c.2.1
                                    have p695_2 := h695c.2.2.1
                                    have p695_3 := h695c.2.2.2
                                    linarith only [h654, h682, hlam, hphi, ht0b, ht34, ht45, ht5b, p695_1, u0elo0, u3ehi2]
                                  · have p695_0 := h695c.1
                                    have p695_1 := h695c.2.1
                                    have p695_2 := h695c.2.2.1
                                    have p695_3 := h695c.2.2.2
                                    linarith only [hlam, p695_0]
                                  · have p695_0 := h695c.1
                                    have p695_1 := h695c.2.1
                                    have p695_2 := h695c.2.2.1
                                    have p695_3 := h695c.2.2.2
                                    linarith only [h0, h654, h682, h687, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p695_1, u3ehi2]
                                  · have p695_0 := h695c.1
                                    have p695_1 := h695c.2.1
                                    have p695_2 := h695c.2.2.1
                                    have p695_3 := h695c.2.2.2
                                    linarith only [h655, hlam, p695_0]
                                  · have p695_0 := h695c.1
                                    have p695_1 := h695c.2.1
                                    have p695_2 := h695c.2.2.1
                                    have p695_3 := h695c.2.2.2
                                    linarith only [h684, hlam, p695_1]
                                  · have p695_0 := h695c.1
                                    have p695_1 := h695c.2.1
                                    have p695_2 := h695c.2.2.1
                                    have p695_3 := h695c.2.2.2
                                    linarith only [h0, h655, h682, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p695_1, u3ehi2]
                                  · have p695_0 := h695c.1
                                    have p695_1 := h695c.2.1
                                    have p695_2 := h695c.2.2.1
                                    have p695_3 := h695c.2.2.2
                                    linarith only [h689, hlam, p695_0]
                                  · have p695_0 := h695c.1
                                    have p695_1 := h695c.2.1
                                    have p695_2 := h695c.2.2.1
                                    have p695_3 := h695c.2.2.2
                                    linarith only [hlam, p695_0]
                                · linarith only [h681, h694, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3, u3ehi3]
                          · linarith only [h0, h654, h681, h682, h685, h689, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                    · linarith only [h0, h684, hc25, hlam, hphi, ht01, ht12, u0ehi5]
                  · linarith only [h0, h653, h682, h683, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                · linarith only [h0, h653, h682, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h732 | h732
                · rcases m.htr 1 2 4 (by decide) (by decide) with h733 | h733
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h734 | h734
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h735 | h735
                      · linarith only [h653, h735, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h737 | h737
                        · linarith only [h0, h654, h657, h735, h737, hc12, hlam, hphi, ht01, u0ehi7]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h739 | h739
                          · linarith only [h0, h654, h681, h739, hc04, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h741 | h741
                            · linarith only [h656, h735, h741, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi1]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h743 | h743
                              · linarith only [h657, h732, h743, hc13, hlam, hphi, ht01, u0ehi7]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h745 | h745
                                · linarith only [h0, h655, h681, h732, h735, h739, h745, hc12, hc34, hlam, hphi, ht01, u0ehi8, u3ehi2]
                                · linarith only [h732, h735, h745, hc45, hlam, hphi, ht34, u3ehi2]
                    · linarith only [h0, h734, hc25, hlam, hphi, ht01, ht12, u0ehi5]
                  · linarith only [h0, h653, h732, h733, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                · linarith only [h0, h653, h732, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
          · linarith only [h0, h653, h656, hlam]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h752 | h752
          · rcases m.htr 0 3 5 (by decide) (by decide) with h753 | h753
            · linarith only [h653, h655, h753, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h755 | h755
              · linarith only [h654, h655, h755, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h757 | h757
                · rcases m.htr 1 2 4 (by decide) (by decide) with h758 | h758
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h759 | h759
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h760 | h760
                      · linarith only [h653, h655, h759, h760, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h762 | h762
                        · linarith only [h654, h655, h753, h759, h760, h762, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                        · linarith only [h654, h655, h760, h762, hc35, hlam, hphi, u3ehi1]
                    · linarith only [h0, h653, h757, h759, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                  · linarith only [h0, h653, h757, h758, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                · linarith only [h0, h653, h757, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
          · linarith only [h0, h653, h752, hlam]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h769 | h769
        · rcases m.htr 0 2 3 (by decide) (by decide) with h770 | h770
          · rcases m.htr 0 3 5 (by decide) (by decide) with h771 | h771
            · rcases m.htr 0 4 5 (by decide) (by decide) with h772 | h772
              · rcases m.htr 1 2 3 (by decide) (by decide) with h773 | h773
                · rcases m.htr 1 2 4 (by decide) (by decide) with h774 | h774
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h775 | h775
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h776 | h776
                      · linarith only [h653, h776, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                      · linarith only [h653, h654, h776, hc34, hlam, hphi, u3ehi1]
                    · linarith only [h653, h654, h771, h774, h775, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi4]
                  · linarith only [h0, h653, h771, h774, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi4]
                · linarith only [h0, h653, h771, h773, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi4]
              · linarith only [h653, h654, h771, h772, hc45, hlam, hphi, ht34, u3ehi4]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h783 | h783
              · rcases m.htr 1 2 3 (by decide) (by decide) with h784 | h784
                · rcases m.htr 1 2 4 (by decide) (by decide) with h785 | h785
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h786 | h786
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h787 | h787
                      · linarith only [h653, h787, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi3]
                      · linarith only [h653, h654, h787, hc34, hlam, hphi, u3ehi1]
                    · linarith only [h653, h654, h784, h785, h786, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                  · linarith only [h0, h653, h784, h785, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                · linarith only [h0, h653, h784, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
              · linarith only [h653, h654, h783, hc45, hlam, hphi, ht34, u3ehi1]
          · linarith only [h0, h653, h770, hlam]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h795 | h795
          · rcases m.htr 0 3 5 (by decide) (by decide) with h796 | h796
            · linarith only [h653, h769, h796, hlam]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h798 | h798
              · rcases m.htr 1 2 3 (by decide) (by decide) with h799 | h799
                · rcases m.htr 1 2 4 (by decide) (by decide) with h800 | h800
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h801 | h801
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h802 | h802
                      · linarith only [h653, h769, h798, h802, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3, u3ehi3]
                      · linarith only [h653, h654, h802, hc34, hlam, hphi, u3ehi1]
                    · linarith only [h653, h654, h799, h800, h801, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                  · linarith only [h0, h653, h799, h800, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
                · linarith only [h0, h653, h799, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
              · linarith only [h653, h654, h798, hc45, hlam, hphi, ht34, u3ehi1]
          · linarith only [h0, h653, h795, hlam]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h810 | h810
      · rcases m.htr 0 1 5 (by decide) (by decide) with h811 | h811
        · rcases m.htr 0 2 3 (by decide) (by decide) with h812 | h812
          · rcases m.htr 0 3 5 (by decide) (by decide) with h813 | h813
            · rcases m.htr 0 4 5 (by decide) (by decide) with h814 | h814
              · rcases m.htr 1 2 3 (by decide) (by decide) with h815 | h815
                · rcases m.htr 1 2 4 (by decide) (by decide) with h816 | h816
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h817 | h817
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h818 | h818
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h819 | h819
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h820 | h820
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h821 | h821
                            · linarith only [h812, h821, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi3]
                            · linarith only [h810, h818, h821, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                          · linarith only [h653, h810, h814, h815, h818, h820, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                        · linarith only [h653, h819, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi5]
                      · linarith only [h653, h810, h814, h818, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi9]
                    · linarith only [h653, h810, h814, h815, h817, hc25, hlam, hphi, ht01, ht12, u0ehi9]
                  · linarith only [h653, h810, h814, h815, h816, hc24, hlam, hphi, ht01, ht12, u0ehi9]
                · linarith only [h0, h810, h814, h815, hc23, hlam, hphi, ht01, ht12, u0ehi9]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h830 | h830
                · rcases m.htr 1 2 4 (by decide) (by decide) with h831 | h831
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h832 | h832
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h833 | h833
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h834 | h834
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h835 | h835
                          · linarith only [h810, h814, h835, hlam, hphi, u0ehi8, u0elo0]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h837 | h837
                            · linarith only [h812, h837, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi3]
                            · linarith only [h653, h810, h830, h833, h837, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                        · linarith only [h653, h834, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi5]
                      · linarith only [h653, h811, h814, h833, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi8]
                    · linarith only [h653, h811, h814, h830, h832, hc25, hlam, hphi, ht01, ht12, u0ehi8]
                  · linarith only [h653, h811, h814, h830, h831, hc24, hlam, hphi, ht01, ht12, u0ehi8]
                · linarith only [h0, h811, h814, h830, hc23, hlam, hphi, ht01, ht12, u0ehi8]
            · linarith only [h653, h811, h813, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h846 | h846
            · rcases m.htr 0 4 5 (by decide) (by decide) with h847 | h847
              · rcases m.htr 1 2 3 (by decide) (by decide) with h848 | h848
                · linarith only [h0, h812, h848, hc12, hlam, hphi, ht01, u0ehi5]
                · linarith only [h0, h810, h847, h848, hc23, hlam, hphi, ht01, ht12, u0ehi9]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h851 | h851
                · linarith only [h0, h812, h851, hc12, hlam, hphi, ht01, u0ehi5]
                · linarith only [h0, h811, h847, h851, hc23, hlam, hphi, ht01, ht12, u0ehi8]
            · linarith only [h0, h811, h812, h846, hlam]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h855 | h855
          · rcases m.htr 0 3 5 (by decide) (by decide) with h856 | h856
            · rcases m.htr 0 4 5 (by decide) (by decide) with h857 | h857
              · linarith only [h810, h811, h857, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h859 | h859
                · rcases m.htr 1 2 4 (by decide) (by decide) with h860 | h860
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h861 | h861
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h862 | h862
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h863 | h863
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h864 | h864
                          · linarith only [h810, h857, h864, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                          · linarith only [h810, h811, h862, h864, hc45, hlam, hphi, ht34, u3ehi3]
                        · linarith only [h855, h856, h863, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi1]
                      · linarith only [h653, h810, h862, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi8]
                    · linarith only [h0, h810, h861, hc25, hlam, hphi, ht01, ht12, u0ehi8]
                  · linarith only [h653, h810, h859, h860, hc24, hlam, hphi, ht01, ht12, u0ehi8]
                · linarith only [h0, h810, h855, h859, hlam, hphi, u0ehi8, u0elo1]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h872 | h872
              · linarith only [h810, h811, h872, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h874 | h874
                · rcases m.htr 1 2 4 (by decide) (by decide) with h875 | h875
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h876 | h876
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h877 | h877
                      · linarith only [h653, h810, h856, h877, hc35, hlam, hphi, u3ehi3]
                      · linarith only [h653, h877, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi5]
                    · linarith only [h653, h810, h874, h876, hc25, hlam, hphi, ht01, ht12, u0ehi8]
                  · linarith only [h653, h810, h874, h875, hc24, hlam, hphi, ht01, ht12, u0ehi8]
                · linarith only [h0, h810, h855, h874, hlam, hphi, u0ehi8, u0elo1]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h883 | h883
            · rcases m.htr 0 4 5 (by decide) (by decide) with h884 | h884
              · linarith only [h810, h811, h884, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h886 | h886
                · linarith only [h855, h886, hc12, hlam, hphi, ht01, u0ehi6]
                · linarith only [h0, h810, h886, hc23, hlam, hphi, ht01, ht12, u0ehi8]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h889 | h889
              · linarith only [h0, h810, h855, h883, h889, hlam]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h891 | h891
                · linarith only [h0, h810, h855, h891, hc12, hlam, hphi, ht01, u0ehi8]
                · linarith only [h0, h810, h891, hc23, hlam, hphi, ht01, ht12, u0ehi8]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h894 | h894
        · rcases m.htr 0 2 3 (by decide) (by decide) with h895 | h895
          · rcases m.htr 0 3 5 (by decide) (by decide) with h896 | h896
            · rcases m.htr 0 4 5 (by decide) (by decide) with h897 | h897
              · rcases m.htr 1 2 3 (by decide) (by decide) with h898 | h898
                · rcases m.htr 1 2 4 (by decide) (by decide) with h899 | h899
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h900 | h900
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h901 | h901
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h902 | h902
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h903 | h903
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h904 | h904
                            · linarith only [h895, h904, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi3]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h906 | h906
                              · linarith only [h898, h901, h904, h906, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi4]
                              · linarith only [h894, h902, h906, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0, u3ehi2]
                          · linarith only [h810, h903, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi5]
                        · linarith only [h810, h901, h902, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi5]
                      · linarith only [h653, h894, h901, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi9]
                    · linarith only [h0, h894, h900, hc25, hlam, hphi, ht01, ht12, u0ehi9]
                  · linarith only [h653, h894, h898, h899, hc24, hlam, hphi, ht01, ht12, u0ehi9]
                · linarith only [h0, h894, h898, hc23, hlam, hphi, ht01, ht12, u0ehi9]
              · linarith only [h810, h894, h897, hlam]
            · linarith only [h653, h894, h896, hlam]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h917 | h917
            · rcases m.htr 0 4 5 (by decide) (by decide) with h918 | h918
              · rcases m.htr 1 2 3 (by decide) (by decide) with h919 | h919
                · linarith only [h895, h919, hc12, hlam, hphi, ht01, u0ehi6]
                · linarith only [h0, h894, h919, hc23, hlam, hphi, ht01, ht12, u0ehi9]
              · linarith only [h810, h894, h918, hlam]
            · linarith only [h653, h894, h917, hlam]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h924 | h924
          · rcases m.htr 0 3 5 (by decide) (by decide) with h925 | h925
            · rcases m.htr 0 4 5 (by decide) (by decide) with h926 | h926
              · rcases m.htr 1 2 3 (by decide) (by decide) with h927 | h927
                · rcases m.htr 1 2 4 (by decide) (by decide) with h928 | h928
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h929 | h929
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h930 | h930
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h931 | h931
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h932 | h932
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h933 | h933
                            · linarith only [h924, h933, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi3]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h935 | h935
                              · linarith only [h927, h930, h933, h935, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi4]
                              · linarith only [h925, h935, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2, u3ehi2]
                          · linarith only [h810, h926, h932, hlam, hphi, u0ehi5, u0elo3]
                        · linarith only [h924, h925, h931, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi1]
                      · linarith only [h653, h930, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi5]
                    · linarith only [h0, h929, hc25, hlam, hphi, ht01, ht12, u0ehi5]
                  · linarith only [h653, h927, h928, hc24, hlam, hphi, ht01, ht12, u0ehi5]
                · linarith only [h0, h927, hc23, hlam, hphi, ht01, ht12, u0ehi5]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h944 | h944
                · rcases m.htr 1 2 4 (by decide) (by decide) with h945 | h945
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h946 | h946
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h947 | h947
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h948 | h948
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h949 | h949
                          · linarith only [h810, h926, h944, h947, h949, hc12, hlam, hphi, ht01, u0ehi5]
                          · linarith only [h810, h949, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi5]
                        · linarith only [h924, h925, h948, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1, u3ehi1]
                      · linarith only [h653, h947, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi5]
                    · linarith only [h0, h946, hc25, hlam, hphi, ht01, ht12, u0ehi5]
                  · linarith only [h653, h944, h945, hc24, hlam, hphi, ht01, ht12, u0ehi5]
                · linarith only [h0, h924, h944, hlam, hphi, u0ehi5, u0elo1]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h957 | h957
              · rcases m.htr 1 2 3 (by decide) (by decide) with h958 | h958
                · rcases m.htr 1 2 4 (by decide) (by decide) with h959 | h959
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h960 | h960
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h961 | h961
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h962 | h962
                        · linarith only [h925, h958, h962, hc12, hlam, hphi, ht01, u0ehi7]
                        · linarith only [h961, h962, hc35, hlam, hphi, u3ehi3]
                      · linarith only [h653, h961, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi5]
                    · linarith only [h0, h960, hc25, hlam, hphi, ht01, ht12, u0ehi5]
                  · linarith only [h653, h958, h959, hc24, hlam, hphi, ht01, ht12, u0ehi5]
                · linarith only [h0, h924, h958, hlam, hphi, u0ehi5, u0elo1]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h969 | h969
                · rcases m.htr 1 2 4 (by decide) (by decide) with h970 | h970
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h971 | h971
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h972 | h972
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h973 | h973
                        · linarith only [h653, h925, h969, h973, hc12, hlam, hphi, ht01, u0ehi5]
                        · linarith only [h972, h973, hc35, hlam, hphi, u3ehi3]
                      · linarith only [h653, h972, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi5]
                    · linarith only [h0, h971, hc25, hlam, hphi, ht01, ht12, u0ehi5]
                  · linarith only [h653, h969, h970, hc24, hlam, hphi, ht01, ht12, u0ehi5]
                · linarith only [h0, h924, h969, hlam, hphi, u0ehi5, u0elo1]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h980 | h980
            · rcases m.htr 0 4 5 (by decide) (by decide) with h981 | h981
              · rcases m.htr 1 2 3 (by decide) (by decide) with h982 | h982
                · linarith only [h924, h982, hc12, hlam, hphi, ht01, u0ehi6]
                · linarith only [h0, h982, hc23, hlam, hphi, ht01, ht12, u0ehi5]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h985 | h985
                · linarith only [h0, h924, h985, hc12, hlam, hphi, ht01, u0ehi5]
                · linarith only [h0, h985, hc23, hlam, hphi, ht01, ht12, u0ehi5]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h988 | h988
              · rcases m.htr 1 2 3 (by decide) (by decide) with h989 | h989
                · linarith only [h0, h924, h989, hc12, hlam, hphi, ht01, u0ehi5]
                · linarith only [h0, h989, hc23, hlam, hphi, ht01, ht12, u0ehi5]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h992 | h992
                · linarith only [h0, h924, h992, hc12, hlam, hphi, ht01, u0ehi5]
                · linarith only [h0, h992, hc23, hlam, hphi, ht01, ht12, u0ehi5]

end R2N4
