import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_11_12_25_L_0_L_R_H_I (m : N7Model)
    (hb1 : CMSig1_7_L_0 m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h1elo := hb1.1
  have h2ehi := hb2.1
  have h5bigk := hb5.1
  have u1elo0 := h1elo (m.d 0 1) (by simp)
  have u1elo1 := h1elo (m.d 1 2) (by simp)
  have u1elo2 := h1elo (m.d 1 3) (by simp)
  have u1elo3 := h1elo (m.d 1 4) (by simp)
  have u1elo4 := h1elo (m.d 1 5) (by simp)
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 2 5 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 3 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 0 4 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 1 2 3 (by decide) (by decide) with h8 | h8
                  · linarith only [h0, h8, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0, u2ehi2]
                  · linarith only [h0, h4, h8, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0, u2ehi1]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h11 | h11
                  · linarith only [h0, h11, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0, u2ehi2]
                  · linarith only [h0, h11, h4, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0, u2ehi1]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h14 | h14
                · rcases m.htr 1 2 3 (by decide) (by decide) with h15 | h15
                  · linarith only [h0, h15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0, u2ehi2]
                  · linarith only [h0, h15, h4, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0, u2ehi1]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h18 | h18
                  · linarith only [h0, h18, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0, u2ehi2]
                  · linarith only [h0, h18, h4, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0, u2ehi1]
            · linarith only [h4, h5, hc25, hlam, hphi, u2ehi2]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h22 | h22
            · linarith only [h22, h4, hc23, hlam, hphi, u2ehi4]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h24 | h24
              · rcases m.htr 0 4 5 (by decide) (by decide) with h25 | h25
                · rcases m.htr 1 2 3 (by decide) (by decide) with h26 | h26
                  · linarith only [h26, h4, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo1, u2ehi0]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h28 | h28
                    · linarith only [h0, h28, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0, u2ehi3]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h30 | h30
                      · linarith only [h0, h22, h30, hlam]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h32 | h32
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h33 | h33
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h34 | h34
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h35 | h35
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h36 | h36
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h37 | h37
                                  · rcases h5bigk with h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c | h38c
                                    · have p38_0 := h38c.1
                                      have p38_1 := h38c.2.1
                                      have p38_2 := h38c.2.2.1
                                      have p38_3 := h38c.2.2.2
                                      linarith only [hlam, p38_0]
                                    · have p38_0 := h38c.1
                                      have p38_1 := h38c.2.1
                                      have p38_2 := h38c.2.2.1
                                      have p38_3 := h38c.2.2.2
                                      linarith only [h1, h24, h30, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p38_1, u1elo0, u2ehi1]
                                    · have p38_0 := h38c.1
                                      have p38_1 := h38c.2.1
                                      have p38_2 := h38c.2.2.1
                                      have p38_3 := h38c.2.2.2
                                      linarith only [h22, hlam, p38_0]
                                    · have p38_0 := h38c.1
                                      have p38_1 := h38c.2.1
                                      have p38_2 := h38c.2.2.1
                                      have p38_3 := h38c.2.2.2
                                      linarith only [h2, h25, h37, hc45, hlam, hphi, ht01, ht0b, ht5b, p38_1, u1elo0]
                                    · have p38_0 := h38c.1
                                      have p38_1 := h38c.2.1
                                      have p38_2 := h38c.2.2.1
                                      have p38_3 := h38c.2.2.2
                                      linarith only [h2, h25, hc45, hlam, hphi, ht01, ht0b, ht5b, p38_1, u1elo0]
                                    · have p38_0 := h38c.1
                                      have p38_1 := h38c.2.1
                                      have p38_2 := h38c.2.2.1
                                      have p38_3 := h38c.2.2.2
                                      linarith only [h3, hlam, p38_0]
                                    · have p38_0 := h38c.1
                                      have p38_1 := h38c.2.1
                                      have p38_2 := h38c.2.2.1
                                      have p38_3 := h38c.2.2.2
                                      linarith only [hlam, p38_0]
                                    · have p38_0 := h38c.1
                                      have p38_1 := h38c.2.1
                                      have p38_2 := h38c.2.2.1
                                      have p38_3 := h38c.2.2.2
                                      linarith only [h30, hlam, p38_0]
                                    · have p38_0 := h38c.1
                                      have p38_1 := h38c.2.1
                                      have p38_2 := h38c.2.2.1
                                      have p38_3 := h38c.2.2.2
                                      linarith only [h37, hc45, hlam, hphi, ht01, ht0b, ht5b, p38_1, u1elo4]
                                    · have p38_0 := h38c.1
                                      have p38_1 := h38c.2.1
                                      have p38_2 := h38c.2.2.1
                                      have p38_3 := h38c.2.2.2
                                      linarith only [h1, h32, hc45, hlam, hphi, ht01, ht0b, ht5b, p38_1, u1elo0]
                                    · have p38_0 := h38c.1
                                      have p38_1 := h38c.2.1
                                      have p38_2 := h38c.2.2.1
                                      have p38_3 := h38c.2.2.2
                                      linarith only [h0, h22, h36, hc24, hlam, hphi, p38_1, u2ehi1]
                                    · have p38_0 := h38c.1
                                      have p38_1 := h38c.2.1
                                      have p38_2 := h38c.2.2.1
                                      have p38_3 := h38c.2.2.2
                                      linarith only [h30, h36, hc24, hlam, hphi, p38_1, u2ehi1]
                                    · have p38_0 := h38c.1
                                      have p38_1 := h38c.2.1
                                      have p38_2 := h38c.2.2.1
                                      have p38_3 := h38c.2.2.2
                                      linarith only [hlam, p38_0]
                                    · have p38_0 := h38c.1
                                      have p38_1 := h38c.2.1
                                      have p38_2 := h38c.2.2.1
                                      have p38_3 := h38c.2.2.2
                                      rcases p38_3 (m.d 0 5) (by simp) with h52 | h52
                                      · linarith only [h22, h52, hlam]
                                      · linarith only [h24, h52, hlam]
                                    · have p38_0 := h38c.1
                                      have p38_1 := h38c.2.1
                                      have p38_2 := h38c.2.2.1
                                      have p38_3 := h38c.2.2.2
                                      rcases p38_3 (m.d 0 5) (by simp) with h55 | h55
                                      · linarith only [h22, h55, hlam]
                                      · linarith only [h25, h55, hlam]
                                    · have p38_0 := h38c.1
                                      have p38_1 := h38c.2.1
                                      have p38_2 := h38c.2.2.1
                                      have p38_3 := h38c.2.2.2
                                      linarith only [h24, hlam, p38_1]
                                    · have p38_0 := h38c.1
                                      have p38_1 := h38c.2.1
                                      have p38_2 := h38c.2.2.1
                                      have p38_3 := h38c.2.2.2
                                      linarith only [h32, hlam, p38_1]
                                    · have p38_0 := h38c.1
                                      have p38_1 := h38c.2.1
                                      have p38_2 := h38c.2.2.1
                                      have p38_3 := h38c.2.2.2
                                      linarith only [h35, hlam, p38_0]
                                    · have p38_0 := h38c.1
                                      have p38_1 := h38c.2.1
                                      have p38_2 := h38c.2.2.1
                                      have p38_3 := h38c.2.2.2
                                      linarith only [hlam, p38_0]
                                    · have p38_0 := h38c.1
                                      have p38_1 := h38c.2.1
                                      have p38_2 := h38c.2.2.1
                                      have p38_3 := h38c.2.2.2
                                      linarith only [h1, h24, hc45, hlam, hphi, ht01, ht0b, ht5b, p38_1, u1elo0]
                                    · have p38_0 := h38c.1
                                      have p38_1 := h38c.2.1
                                      have p38_2 := h38c.2.2.1
                                      have p38_3 := h38c.2.2.2
                                      linarith only [h25, hlam, p38_1]
                                    · have p38_0 := h38c.1
                                      have p38_1 := h38c.2.1
                                      have p38_2 := h38c.2.2.1
                                      have p38_3 := h38c.2.2.2
                                      linarith only [h33, hlam, p38_1]
                                    · have p38_0 := h38c.1
                                      have p38_1 := h38c.2.1
                                      have p38_2 := h38c.2.2.1
                                      have p38_3 := h38c.2.2.2
                                      linarith only [h36, hlam, p38_1]
                                    · have p38_0 := h38c.1
                                      have p38_1 := h38c.2.1
                                      have p38_2 := h38c.2.2.1
                                      have p38_3 := h38c.2.2.2
                                      linarith only [h37, hlam, p38_1]
                                    · have p38_0 := h38c.1
                                      have p38_1 := h38c.2.1
                                      have p38_2 := h38c.2.2.1
                                      have p38_3 := h38c.2.2.2
                                      linarith only [hlam, p38_0]
                                  · linarith only [h2, h33, h37, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                                · linarith only [h2, h33, h36, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                              · linarith only [h1, h32, h35, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                            · linarith only [h0, h34, h4, hc34, hlam, hphi, ht23, u2ehi1]
                          · linarith only [h2, h25, h28, h33, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0, u2ehi1]
                        · linarith only [h24, h26, h32, h4, hc23, hlam, hphi, u2ehi1]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h74 | h74
                  · linarith only [h0, h74, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0, u2ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h76 | h76
                    · linarith only [h0, h76, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0, u2ehi3]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h78 | h78
                      · linarith only [h1, h74, h78, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0, u2ehi4]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h80 | h80
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h81 | h81
                          · linarith only [h2, h25, h81, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h83 | h83
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h84 | h84
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h85 | h85
                                · linarith only [h2, h25, h76, h85, hc24, hlam, hphi, u2ehi1]
                                · linarith only [h76, h85, hc45, hlam, hphi, ht23, ht34, u2ehi1]
                              · linarith only [h1, h80, h84, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                            · linarith only [h0, h4, h83, hc34, hlam, hphi, ht23, u2ehi1]
                        · linarith only [h1, h24, h74, h80, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0, u2ehi1]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h91 | h91
                · rcases m.htr 1 2 3 (by decide) (by decide) with h92 | h92
                  · linarith only [h0, h92, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0, u2ehi2]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h94 | h94
                    · linarith only [h1, h92, h94, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0, u2ehi3]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h96 | h96
                      · linarith only [h1, h92, h96, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0, u2ehi4]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h98 | h98
                        · linarith only [h1, h24, h98, hc03, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo0]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h100 | h100
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h101 | h101
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h102 | h102
                              · linarith only [h1, h102, h24, h92, hc23, hlam, hphi, u2ehi1]
                              · linarith only [h102, h4, hc35, hlam, hphi, ht23, u2ehi0]
                            · linarith only [h0, h101, h4, hc34, hlam, hphi, ht23, u2ehi1]
                          · linarith only [h100, h2, h91, h94, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo0, u2ehi1]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h107 | h107
                  · linarith only [h0, h107, h4, hlam]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h109 | h109
                    · linarith only [h0, h109, h4, hc23, hlam, hphi, u2ehi3]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h111 | h111
                      · linarith only [h109, h111, hc24, hlam, hphi, u2ehi4]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h113 | h113
                        · linarith only [h113, h24, h4, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2, u2ehi0]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h115 | h115
                          · linarith only [h115, h2, h91, hc04, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo0]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h117 | h117
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h118 | h118
                              · linarith only [h118, h24, h4, hc23, hlam, hphi, u2ehi0]
                              · linarith only [h0, h118, h4, hc35, hlam, hphi, ht23, u2ehi1]
                            · linarith only [h0, h117, h4, hc34, hlam, hphi, ht23, u2ehi1]
        · linarith only [h0, h3, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo4, u2ehi1]
      · linarith only [h0, h2, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo3, u2ehi1]
    · linarith only [h0, h1, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2, u2ehi1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h125 | h125
    · rcases m.htr 0 1 4 (by decide) (by decide) with h126 | h126
      · rcases m.htr 0 1 5 (by decide) (by decide) with h127 | h127
        · rcases m.htr 0 2 3 (by decide) (by decide) with h128 | h128
          · rcases m.htr 0 2 5 (by decide) (by decide) with h129 | h129
            · rcases m.htr 0 3 5 (by decide) (by decide) with h130 | h130
              · rcases m.htr 0 4 5 (by decide) (by decide) with h131 | h131
                · rcases m.htr 1 2 3 (by decide) (by decide) with h132 | h132
                  · linarith only [h0, h125, h132, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo1, u2ehi2]
                  · linarith only [h0, h125, h128, h132, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h135 | h135
                  · linarith only [h0, h125, h135, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo1, u2ehi2]
                  · linarith only [h0, h125, h129, h130, h135, hc23, hlam, hphi, u2ehi4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h138 | h138
                · rcases m.htr 1 2 3 (by decide) (by decide) with h139 | h139
                  · linarith only [h0, h125, h139, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo1, u2ehi2]
                  · linarith only [h0, h125, h128, h130, h139, hc13, hc35, hlam, hphi]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h142 | h142
                  · linarith only [h0, h125, h142, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo1, u2ehi2]
                  · linarith only [h0, h125, h128, h130, h142, hc13, hc35, hlam, hphi]
            · linarith only [h128, h129, hc25, hlam, hphi, u2ehi2]
          · linarith only [h0, h125, h128, hlam]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h147 | h147
          · rcases m.htr 0 2 5 (by decide) (by decide) with h148 | h148
            · rcases m.htr 0 3 5 (by decide) (by decide) with h149 | h149
              · linarith only [h125, h127, h149, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h151 | h151
                · linarith only [h126, h127, h151, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h153 | h153
                  · linarith only [h0, h125, h153, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo1, u2ehi2]
                  · linarith only [h0, h125, h147, h153, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
            · linarith only [h147, h148, hc25, hlam, hphi, u2ehi2]
          · linarith only [h0, h125, h147, hlam]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h158 | h158
        · rcases m.htr 0 2 3 (by decide) (by decide) with h159 | h159
          · rcases m.htr 0 2 5 (by decide) (by decide) with h160 | h160
            · rcases m.htr 0 3 5 (by decide) (by decide) with h161 | h161
              · rcases m.htr 0 4 5 (by decide) (by decide) with h162 | h162
                · rcases m.htr 1 2 3 (by decide) (by decide) with h163 | h163
                  · linarith only [h125, h126, h163, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo3, u2ehi2]
                  · linarith only [h0, h125, h159, h163, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                · linarith only [h125, h126, h161, h162, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h167 | h167
                · rcases m.htr 1 2 3 (by decide) (by decide) with h168 | h168
                  · linarith only [h125, h126, h168, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo3, u2ehi2]
                  · linarith only [h0, h159, h161, h168, hc35, hlam, hphi, ht23, u2ehi0]
                · linarith only [h126, h158, h167, hlam]
            · linarith only [h159, h160, hc25, hlam, hphi, u2ehi2]
          · linarith only [h0, h125, h159, hlam]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h174 | h174
          · rcases m.htr 0 2 5 (by decide) (by decide) with h175 | h175
            · rcases m.htr 0 3 5 (by decide) (by decide) with h176 | h176
              · linarith only [h125, h158, h176, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h178 | h178
                · rcases m.htr 1 2 3 (by decide) (by decide) with h179 | h179
                  · linarith only [h125, h126, h179, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo3, u2ehi2]
                  · linarith only [h0, h125, h174, h179, hc02, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h182 | h182
                  · linarith only [h125, h126, h182, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo3, u2ehi2]
                  · linarith only [h0, h174, h176, h182, hc35, hlam, hphi, ht23, u2ehi0]
            · linarith only [h174, h175, hc25, hlam, hphi, u2ehi2]
          · linarith only [h0, h125, h174, hlam]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h187 | h187
      · rcases m.htr 0 1 5 (by decide) (by decide) with h188 | h188
        · rcases m.htr 0 2 3 (by decide) (by decide) with h189 | h189
          · rcases m.htr 0 2 5 (by decide) (by decide) with h190 | h190
            · rcases m.htr 0 3 5 (by decide) (by decide) with h191 | h191
              · rcases m.htr 0 4 5 (by decide) (by decide) with h192 | h192
                · rcases m.htr 1 2 3 (by decide) (by decide) with h193 | h193
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h194 | h194
                    · linarith only [h125, h187, h193, h194, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo1, u2ehi3]
                    · linarith only [h0, h189, h194, hc24, hlam, hphi, u2ehi2]
                  · linarith only [h0, h189, h193, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h198 | h198
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h199 | h199
                    · linarith only [h125, h187, h199, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2, u2ehi3]
                    · linarith only [h0, h189, h199, hc24, hlam, hphi, u2ehi2]
                  · linarith only [h0, h189, h198, hlam]
              · linarith only [h125, h188, h191, hlam]
            · linarith only [h189, h190, hc25, hlam, hphi, u2ehi2]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h205 | h205
            · linarith only [h189, h205, hc23, hlam, hphi, u2ehi4]
            · linarith only [h0, h188, h205, hlam]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h208 | h208
          · rcases m.htr 0 2 5 (by decide) (by decide) with h209 | h209
            · rcases m.htr 0 3 5 (by decide) (by decide) with h210 | h210
              · rcases m.htr 0 4 5 (by decide) (by decide) with h211 | h211
                · linarith only [h187, h188, h211, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h213 | h213
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h214 | h214
                    · linarith only [h125, h187, h214, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2, u2ehi3]
                    · linarith only [h0, h209, h214, hc24, hlam, hphi, u2ehi4]
                  · linarith only [h0, h209, h213, hc23, hlam, hphi, u2ehi4]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h218 | h218
                · linarith only [h125, h187, h210, h218, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h220 | h220
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h221 | h221
                    · linarith only [h187, h188, h221, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo4, u2ehi3]
                    · linarith only [h0, h209, h221, hc24, hlam, hphi, u2ehi4]
                  · linarith only [h0, h208, h220, hlam]
            · linarith only [h208, h209, hc25, hlam, hphi, u2ehi2]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h226 | h226
            · linarith only [h208, h226, hc23, hlam, hphi, u2ehi4]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h228 | h228
              · rcases m.htr 0 4 5 (by decide) (by decide) with h229 | h229
                · linarith only [h0, h187, h226, h229, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h231 | h231
                  · linarith only [h208, h231, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo1, u2ehi0]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h233 | h233
                    · linarith only [h231, h233, hc23, hlam, hphi, u2ehi3]
                    · linarith only [h0, h187, h233, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h236 | h236
                · linarith only [h125, h187, h228, h236, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h238 | h238
                  · linarith only [h208, h238, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo1, u2ehi0]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h240 | h240
                    · linarith only [h238, h240, hc23, hlam, hphi, u2ehi3]
                    · linarith only [h0, h187, h240, hlam]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h243 | h243
        · rcases m.htr 0 2 3 (by decide) (by decide) with h244 | h244
          · rcases m.htr 0 2 5 (by decide) (by decide) with h245 | h245
            · rcases m.htr 0 3 5 (by decide) (by decide) with h246 | h246
              · rcases m.htr 0 4 5 (by decide) (by decide) with h247 | h247
                · rcases m.htr 1 2 3 (by decide) (by decide) with h248 | h248
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h249 | h249
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h250 | h250
                      · linarith only [h125, h243, h248, h250, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo1, u2ehi4]
                      · linarith only [h249, h250, hc25, hlam, hphi, u2ehi3]
                    · linarith only [h125, h243, h245, h248, h249, hc24, hlam, hphi, u2ehi4]
                  · linarith only [h0, h244, h248, hlam]
                · linarith only [h187, h243, h247, hlam]
              · linarith only [h125, h243, h246, hlam]
            · linarith only [h244, h245, hc25, hlam, hphi, u2ehi2]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h258 | h258
            · linarith only [h244, h258, hc23, hlam, hphi, u2ehi4]
            · linarith only [h0, h243, h258, hlam]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h261 | h261
          · rcases m.htr 0 2 5 (by decide) (by decide) with h262 | h262
            · rcases m.htr 0 3 5 (by decide) (by decide) with h263 | h263
              · rcases m.htr 0 4 5 (by decide) (by decide) with h264 | h264
                · rcases m.htr 1 2 3 (by decide) (by decide) with h265 | h265
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h266 | h266
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h267 | h267
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h268 | h268
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h269 | h269
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h270 | h270
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h271 | h271
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h272 | h272
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h273 | h273
                                  · linarith only [h0, h261, h270, h273, hc45, hlam, hphi, ht01, ht0b, ht5b, u1elo1]
                                  · linarith only [h0, h261, h270, h272, h273, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo1]
                                · linarith only [h187, h264, h272, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo3, u2ehi3]
                              · linarith only [h0, h261, h263, h271, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo1, u2ehi2]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h278 | h278
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h279 | h279
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h280 | h280
                                  · rcases h5bigk with h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c | h281c
                                    · have p281_0 := h281c.1
                                      have p281_1 := h281c.2.1
                                      have p281_2 := h281c.2.2.1
                                      have p281_3 := h281c.2.2.2
                                      linarith only [hlam, p281_0]
                                    · have p281_0 := h281c.1
                                      have p281_1 := h281c.2.1
                                      have p281_2 := h281c.2.2.1
                                      have p281_3 := h281c.2.2.2
                                      linarith only [h243, hlam, p281_1]
                                    · have p281_0 := h281c.1
                                      have p281_1 := h281c.2.1
                                      have p281_2 := h281c.2.2.1
                                      have p281_3 := h281c.2.2.2
                                      linarith only [hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p281_1, u2ehi4]
                                    · have p281_0 := h281c.1
                                      have p281_1 := h281c.2.1
                                      have p281_2 := h281c.2.2.1
                                      have p281_3 := h281c.2.2.2
                                      linarith only [h243, h268, hc35, hlam, hphi, ht01, ht0b, ht5b, p281_1, u1elo2]
                                    · have p281_0 := h281c.1
                                      have p281_1 := h281c.2.1
                                      have p281_2 := h281c.2.2.1
                                      have p281_3 := h281c.2.2.2
                                      linarith only [h0, h261, h263, hc45, hlam, hphi, ht01, ht0b, ht5b, p281_1, u1elo1]
                                    · have p281_0 := h281c.1
                                      have p281_1 := h281c.2.1
                                      have p281_2 := h281c.2.2.1
                                      have p281_3 := h281c.2.2.2
                                      linarith only [h268, hc05, hlam, hphi, ht01, ht0b, ht5b, p281_1, u1elo2]
                                    · have p281_0 := h281c.1
                                      have p281_1 := h281c.2.1
                                      have p281_2 := h281c.2.2.1
                                      have p281_3 := h281c.2.2.2
                                      linarith only [hlam, p281_0]
                                    · have p281_0 := h281c.1
                                      have p281_1 := h281c.2.1
                                      have p281_2 := h281c.2.2.1
                                      have p281_3 := h281c.2.2.2
                                      linarith only [h265, h268, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p281_1, u1elo1, u2ehi4]
                                    · have p281_0 := h281c.1
                                      have p281_1 := h281c.2.1
                                      have p281_2 := h281c.2.2.1
                                      have p281_3 := h281c.2.2.2
                                      linarith only [h265, h268, h280, hc45, hlam, hphi, ht01, ht0b, ht5b, p281_1, u1elo1]
                                    · have p281_0 := h281c.1
                                      have p281_1 := h281c.2.1
                                      have p281_2 := h281c.2.2.1
                                      have p281_3 := h281c.2.2.2
                                      linarith only [h265, h268, hc45, hlam, hphi, ht01, ht0b, ht5b, p281_1, u1elo1]
                                    · have p281_0 := h281c.1
                                      have p281_1 := h281c.2.1
                                      have p281_2 := h281c.2.2.1
                                      have p281_3 := h281c.2.2.2
                                      linarith only [h262, hlam, p281_1]
                                    · have p281_0 := h281c.1
                                      have p281_1 := h281c.2.1
                                      have p281_2 := h281c.2.2.1
                                      have p281_3 := h281c.2.2.2
                                      linarith only [h267, hlam, p281_1]
                                    · have p281_0 := h281c.1
                                      have p281_1 := h281c.2.1
                                      have p281_2 := h281c.2.2.1
                                      have p281_3 := h281c.2.2.2
                                      linarith only [hlam, p281_0]
                                    · have p281_0 := h281c.1
                                      have p281_1 := h281c.2.1
                                      have p281_2 := h281c.2.2.1
                                      have p281_3 := h281c.2.2.2
                                      linarith only [h270, h278, h280, hc34, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p281_1]
                                    · have p281_0 := h281c.1
                                      have p281_1 := h281c.2.1
                                      have p281_2 := h281c.2.2.1
                                      have p281_3 := h281c.2.2.2
                                      linarith only [h0, h261, h278, hc45, hlam, hphi, ht01, ht0b, ht5b, p281_1, u1elo1]
                                    · have p281_0 := h281c.1
                                      have p281_1 := h281c.2.1
                                      have p281_2 := h281c.2.2.1
                                      have p281_3 := h281c.2.2.2
                                      linarith only [h263, hlam, p281_1]
                                    · have p281_0 := h281c.1
                                      have p281_1 := h281c.2.1
                                      have p281_2 := h281c.2.2.1
                                      have p281_3 := h281c.2.2.2
                                      linarith only [h268, hlam, p281_1]
                                    · have p281_0 := h281c.1
                                      have p281_1 := h281c.2.1
                                      have p281_2 := h281c.2.2.1
                                      have p281_3 := h281c.2.2.2
                                      linarith only [h278, hlam, p281_0]
                                    · have p281_0 := h281c.1
                                      have p281_1 := h281c.2.1
                                      have p281_2 := h281c.2.2.1
                                      have p281_3 := h281c.2.2.2
                                      linarith only [hlam, p281_0]
                                    · have p281_0 := h281c.1
                                      have p281_1 := h281c.2.1
                                      have p281_2 := h281c.2.2.1
                                      have p281_3 := h281c.2.2.2
                                      linarith only [h0, h261, h263, hc45, hlam, hphi, ht01, ht0b, ht5b, p281_1, u1elo1]
                                    · have p281_0 := h281c.1
                                      have p281_1 := h281c.2.1
                                      have p281_2 := h281c.2.2.1
                                      have p281_3 := h281c.2.2.2
                                      linarith only [h264, hlam, p281_1]
                                    · have p281_0 := h281c.1
                                      have p281_1 := h281c.2.1
                                      have p281_2 := h281c.2.2.1
                                      have p281_3 := h281c.2.2.2
                                      linarith only [h269, hlam, p281_1]
                                    · have p281_0 := h281c.1
                                      have p281_1 := h281c.2.1
                                      have p281_2 := h281c.2.2.1
                                      have p281_3 := h281c.2.2.2
                                      linarith only [h279, hlam, p281_1]
                                    · have p281_0 := h281c.1
                                      have p281_1 := h281c.2.1
                                      have p281_2 := h281c.2.2.1
                                      have p281_3 := h281c.2.2.2
                                      linarith only [h280, hlam, p281_1]
                                    · have p281_0 := h281c.1
                                      have p281_1 := h281c.2.1
                                      have p281_2 := h281c.2.2.1
                                      have p281_3 := h281c.2.2.2
                                      linarith only [hlam, p281_0]
                                  · linarith only [h270, h278, h280, hc45, hlam, hphi, ht23, ht34, u2ehi4]
                                · linarith only [h187, h264, h266, h270, h278, h279, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo1, u2ehi4]
                              · linarith only [h0, h261, h263, h278, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo1, u2ehi2]
                          · linarith only [h187, h264, h269, hlam]
                        · linarith only [h0, h125, h261, h263, h268, hc01, hlam, hphi, u1elo1]
                      · linarith only [h0, h243, h262, h267, hc01, hlam, hphi, u1elo4]
                    · linarith only [h0, h261, h266, hc24, hlam, hphi, u2ehi2]
                  · linarith only [h0, h261, h265, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h315 | h315
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h316 | h316
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h317 | h317
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h318 | h318
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h319 | h319
                          · linarith only [h187, h264, h319, hc01, hlam, hphi, u1elo3]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h321 | h321
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h322 | h322
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h323 | h323
                                · linarith only [h0, h187, h261, h264, h321, h323, hc01, hlam, hphi, u1elo1]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h325 | h325
                                  · linarith only [h0, h187, h261, h319, h321, h325, hc01, hlam, hphi, u1elo1]
                                  · rcases h5bigk with h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c | h327c
                                    · have p327_0 := h327c.1
                                      have p327_1 := h327c.2.1
                                      have p327_2 := h327c.2.2.1
                                      have p327_3 := h327c.2.2.2
                                      linarith only [hlam, p327_0]
                                    · have p327_0 := h327c.1
                                      have p327_1 := h327c.2.1
                                      have p327_2 := h327c.2.2.1
                                      have p327_3 := h327c.2.2.2
                                      linarith only [h243, hlam, p327_1]
                                    · have p327_0 := h327c.1
                                      have p327_1 := h327c.2.1
                                      have p327_2 := h327c.2.2.1
                                      have p327_3 := h327c.2.2.2
                                      linarith only [h125, h263, h323, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b, p327_1, u1elo2]
                                    · have p327_0 := h327c.1
                                      have p327_1 := h327c.2.1
                                      have p327_2 := h327c.2.2.1
                                      have p327_3 := h327c.2.2.2
                                      linarith only [h0, h261, h263, h325, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p327_1, u1elo1]
                                    · have p327_0 := h327c.1
                                      have p327_1 := h327c.2.1
                                      have p327_2 := h327c.2.2.1
                                      have p327_3 := h327c.2.2.2
                                      linarith only [h264, hlam, p327_0]
                                    · have p327_0 := h327c.1
                                      have p327_1 := h327c.2.1
                                      have p327_2 := h327c.2.2.1
                                      have p327_3 := h327c.2.2.2
                                      linarith only [hc05, hlam, hphi, ht01, ht0b, ht5b, p327_1, u1elo4]
                                    · have p327_0 := h327c.1
                                      have p327_1 := h327c.2.1
                                      have p327_2 := h327c.2.2.1
                                      have p327_3 := h327c.2.2.2
                                      linarith only [hlam, p327_0]
                                    · have p327_0 := h327c.1
                                      have p327_1 := h327c.2.1
                                      have p327_2 := h327c.2.2.1
                                      have p327_3 := h327c.2.2.2
                                      linarith only [h317, h323, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p327_1, u1elo1, u2ehi3]
                                    · have p327_0 := h327c.1
                                      have p327_1 := h327c.2.1
                                      have p327_2 := h327c.2.2.1
                                      have p327_3 := h327c.2.2.2
                                      linarith only [h315, h318, h325, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p327_1, u1elo1]
                                    · have p327_0 := h327c.1
                                      have p327_1 := h327c.2.1
                                      have p327_2 := h327c.2.2.1
                                      have p327_3 := h327c.2.2.2
                                      linarith only [h319, hlam, p327_0]
                                    · have p327_0 := h327c.1
                                      have p327_1 := h327c.2.1
                                      have p327_2 := h327c.2.2.1
                                      have p327_3 := h327c.2.2.2
                                      linarith only [h262, hlam, p327_1]
                                    · have p327_0 := h327c.1
                                      have p327_1 := h327c.2.1
                                      have p327_2 := h327c.2.2.1
                                      have p327_3 := h327c.2.2.2
                                      linarith only [h317, hlam, p327_1]
                                    · have p327_0 := h327c.1
                                      have p327_1 := h327c.2.1
                                      have p327_2 := h327c.2.2.1
                                      have p327_3 := h327c.2.2.2
                                      linarith only [hlam, p327_0]
                                    · have p327_0 := h327c.1
                                      have p327_1 := h327c.2.1
                                      have p327_2 := h327c.2.2.1
                                      have p327_3 := h327c.2.2.2
                                      linarith only [h243, h262, h315, h318, h325, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p327_1, u1elo1]
                                    · have p327_0 := h327c.1
                                      have p327_1 := h327c.2.1
                                      have p327_2 := h327c.2.2.1
                                      have p327_3 := h327c.2.2.2
                                      linarith only [h323, hlam, p327_0]
                                    · have p327_0 := h327c.1
                                      have p327_1 := h327c.2.1
                                      have p327_2 := h327c.2.2.1
                                      have p327_3 := h327c.2.2.2
                                      linarith only [h263, hlam, p327_1]
                                    · have p327_0 := h327c.1
                                      have p327_1 := h327c.2.1
                                      have p327_2 := h327c.2.2.1
                                      have p327_3 := h327c.2.2.2
                                      linarith only [h318, hlam, p327_1]
                                    · have p327_0 := h327c.1
                                      have p327_1 := h327c.2.1
                                      have p327_2 := h327c.2.2.1
                                      have p327_3 := h327c.2.2.2
                                      linarith only [h322, hlam, p327_0]
                                    · have p327_0 := h327c.1
                                      have p327_1 := h327c.2.1
                                      have p327_2 := h327c.2.2.1
                                      have p327_3 := h327c.2.2.2
                                      linarith only [hlam, p327_0]
                                    · have p327_0 := h327c.1
                                      have p327_1 := h327c.2.1
                                      have p327_2 := h327c.2.2.1
                                      have p327_3 := h327c.2.2.2
                                      linarith only [h325, hlam, p327_0]
                                    · have p327_0 := h327c.1
                                      have p327_1 := h327c.2.1
                                      have p327_2 := h327c.2.2.1
                                      have p327_3 := h327c.2.2.2
                                      linarith only [h243, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p327_1]
                                    · have p327_0 := h327c.1
                                      have p327_1 := h327c.2.1
                                      have p327_2 := h327c.2.2.1
                                      have p327_3 := h327c.2.2.2
                                      linarith only [h0, h243, h261, hc01, hc45, hlam, hphi, ht23, ht34, p327_1, u1elo1, u2ehi2]
                                    · have p327_0 := h327c.1
                                      have p327_1 := h327c.2.1
                                      have p327_2 := h327c.2.2.1
                                      have p327_3 := h327c.2.2.2
                                      linarith only [hc45, hlam, hphi, ht23, ht34, p327_1, u2ehi4]
                                    · have p327_0 := h327c.1
                                      have p327_1 := h327c.2.1
                                      have p327_2 := h327c.2.2.1
                                      have p327_3 := h327c.2.2.2
                                      linarith only [h325, hc34, hc45, hlam, hphi, p327_1]
                                    · have p327_0 := h327c.1
                                      have p327_1 := h327c.2.1
                                      have p327_2 := h327c.2.2.1
                                      have p327_3 := h327c.2.2.2
                                      linarith only [hlam, p327_0]
                              · linarith only [h0, h261, h263, h322, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo1, u2ehi2]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h354 | h354
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h355 | h355
                                · linarith only [h187, h264, h316, h355, hc01, hlam, hphi, u1elo1]
                                · linarith only [h321, h354, h355, hlam]
                              · linarith only [h0, h261, h263, h354, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo1, u2ehi2]
                        · linarith only [h0, h125, h261, h263, h318, hc01, hlam, hphi, u1elo1]
                      · linarith only [h0, h261, h317, hc25, hlam, hphi, u2ehi2]
                    · linarith only [h0, h261, h316, hc24, hlam, hphi, u2ehi2]
                  · linarith only [h0, h261, h315, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h363 | h363
                · rcases m.htr 1 2 3 (by decide) (by decide) with h364 | h364
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h365 | h365
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h366 | h366
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h367 | h367
                        · linarith only [h125, h263, h367, hc01, hlam, hphi, u1elo2]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h369 | h369
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h370 | h370
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h371 | h371
                              · linarith only [h125, h367, h371, hc01, hc23, hlam, hphi, ht12]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h373 | h373
                                · linarith only [h370, h371, h373, hlam]
                                · linarith only [h187, h363, h373, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo3, u2ehi3]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h376 | h376
                              · linarith only [h125, h367, h370, h376, hc03, hc34, hlam, hphi]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h378 | h378
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h379 | h379
                                  · rcases h5bigk with h380c | h380c | h380c | h380c | h380c | h380c | h380c | h380c | h380c | h380c | h380c | h380c | h380c | h380c | h380c | h380c | h380c | h380c | h380c | h380c | h380c | h380c | h380c | h380c | h380c
                                    · have p380_0 := h380c.1
                                      have p380_1 := h380c.2.1
                                      have p380_2 := h380c.2.2.1
                                      have p380_3 := h380c.2.2.2
                                      linarith only [hlam, p380_0]
                                    · have p380_0 := h380c.1
                                      have p380_1 := h380c.2.1
                                      have p380_2 := h380c.2.2.1
                                      have p380_3 := h380c.2.2.2
                                      linarith only [h243, hlam, p380_1]
                                    · have p380_0 := h380c.1
                                      have p380_1 := h380c.2.1
                                      have p380_2 := h380c.2.2.1
                                      have p380_3 := h380c.2.2.2
                                      linarith only [hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p380_1, u2ehi4]
                                    · have p380_0 := h380c.1
                                      have p380_1 := h380c.2.1
                                      have p380_2 := h380c.2.2.1
                                      have p380_3 := h380c.2.2.2
                                      linarith only [h263, hlam, p380_0]
                                    · have p380_0 := h380c.1
                                      have p380_1 := h380c.2.1
                                      have p380_2 := h380c.2.2.1
                                      have p380_3 := h380c.2.2.2
                                      linarith only [h243, hc45, hlam, hphi, ht01, ht0b, ht5b, p380_1, u1elo4]
                                    · have p380_0 := h380c.1
                                      have p380_1 := h380c.2.1
                                      have p380_2 := h380c.2.2.1
                                      have p380_3 := h380c.2.2.2
                                      linarith only [hc05, hlam, hphi, ht01, ht0b, ht5b, p380_1, u1elo4]
                                    · have p380_0 := h380c.1
                                      have p380_1 := h380c.2.1
                                      have p380_2 := h380c.2.2.1
                                      have p380_3 := h380c.2.2.2
                                      linarith only [hlam, p380_0]
                                    · have p380_0 := h380c.1
                                      have p380_1 := h380c.2.1
                                      have p380_2 := h380c.2.2.1
                                      have p380_3 := h380c.2.2.2
                                      linarith only [h366, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p380_1, u1elo1, u2ehi4]
                                    · have p380_0 := h380c.1
                                      have p380_1 := h380c.2.1
                                      have p380_2 := h380c.2.2.1
                                      have p380_3 := h380c.2.2.2
                                      linarith only [h367, hlam, p380_0]
                                    · have p380_0 := h380c.1
                                      have p380_1 := h380c.2.1
                                      have p380_2 := h380c.2.2.1
                                      have p380_3 := h380c.2.2.2
                                      linarith only [h365, h369, hc45, hlam, hphi, ht01, ht0b, ht5b, p380_1, u1elo1]
                                    · have p380_0 := h380c.1
                                      have p380_1 := h380c.2.1
                                      have p380_2 := h380c.2.2.1
                                      have p380_3 := h380c.2.2.2
                                      linarith only [h262, hlam, p380_1]
                                    · have p380_0 := h380c.1
                                      have p380_1 := h380c.2.1
                                      have p380_2 := h380c.2.2.1
                                      have p380_3 := h380c.2.2.2
                                      linarith only [h366, hlam, p380_1]
                                    · have p380_0 := h380c.1
                                      have p380_1 := h380c.2.1
                                      have p380_2 := h380c.2.2.1
                                      have p380_3 := h380c.2.2.2
                                      linarith only [hlam, p380_0]
                                    · have p380_0 := h380c.1
                                      have p380_1 := h380c.2.1
                                      have p380_2 := h380c.2.2.1
                                      have p380_3 := h380c.2.2.2
                                      linarith only [h376, hlam, p380_1]
                                    · have p380_0 := h380c.1
                                      have p380_1 := h380c.2.1
                                      have p380_2 := h380c.2.2.1
                                      have p380_3 := h380c.2.2.2
                                      linarith only [h0, h262, hc45, hlam, hphi, ht01, ht0b, ht5b, p380_1, u1elo1]
                                    · have p380_0 := h380c.1
                                      have p380_1 := h380c.2.1
                                      have p380_2 := h380c.2.2.1
                                      have p380_3 := h380c.2.2.2
                                      linarith only [h262, hc35, hlam, hphi, ht23, p380_1, u2ehi4]
                                    · have p380_0 := h380c.1
                                      have p380_1 := h380c.2.1
                                      have p380_2 := h380c.2.2.1
                                      have p380_3 := h380c.2.2.2
                                      linarith only [h243, hc01, hc35, hlam, hphi, ht12, ht23, p380_1]
                                    · have p380_0 := h380c.1
                                      have p380_1 := h380c.2.1
                                      have p380_2 := h380c.2.2.1
                                      have p380_3 := h380c.2.2.2
                                      linarith only [hc35, hlam, hphi, ht23, p380_1, u2ehi4]
                                    · have p380_0 := h380c.1
                                      have p380_1 := h380c.2.1
                                      have p380_2 := h380c.2.2.1
                                      have p380_3 := h380c.2.2.2
                                      linarith only [hlam, p380_0]
                                    · have p380_0 := h380c.1
                                      have p380_1 := h380c.2.1
                                      have p380_2 := h380c.2.2.1
                                      have p380_3 := h380c.2.2.2
                                      rcases p380_3 (m.d 0 5) (by simp) with h400 | h400
                                      · linarith only [h263, h400, hlam]
                                      · linarith only [h363, h400, hlam]
                                    · have p380_0 := h380c.1
                                      have p380_1 := h380c.2.1
                                      have p380_2 := h380c.2.2.1
                                      have p380_3 := h380c.2.2.2
                                      linarith only [h363, hlam, p380_1]
                                    · have p380_0 := h380c.1
                                      have p380_1 := h380c.2.1
                                      have p380_2 := h380c.2.2.1
                                      have p380_3 := h380c.2.2.2
                                      linarith only [h369, hlam, p380_1]
                                    · have p380_0 := h380c.1
                                      have p380_1 := h380c.2.1
                                      have p380_2 := h380c.2.2.1
                                      have p380_3 := h380c.2.2.2
                                      linarith only [h378, hlam, p380_1]
                                    · have p380_0 := h380c.1
                                      have p380_1 := h380c.2.1
                                      have p380_2 := h380c.2.2.1
                                      have p380_3 := h380c.2.2.2
                                      linarith only [h379, hlam, p380_1]
                                    · have p380_0 := h380c.1
                                      have p380_1 := h380c.2.1
                                      have p380_2 := h380c.2.2.1
                                      have p380_3 := h380c.2.2.2
                                      linarith only [hlam, p380_0]
                                  · linarith only [h370, h379, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                                · linarith only [h187, h363, h365, h378, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo1, u2ehi3]
                          · linarith only [h187, h363, h369, hlam]
                      · linarith only [h0, h262, h366, hlam]
                    · linarith only [h0, h262, h365, hc24, hlam, hphi, u2ehi4]
                  · linarith only [h0, h125, h261, h262, h364, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2, u2ehi4]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h414 | h414
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h415 | h415
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h416 | h416
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h417 | h417
                        · linarith only [h261, h263, h414, h417, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo1, u2ehi2]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h419 | h419
                          · linarith only [h187, h363, h419, hc01, hlam, hphi, u1elo3]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h421 | h421
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h422 | h422
                              · linarith only [h0, h261, h417, h422, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u1elo1]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h424 | h424
                                · linarith only [h0, h187, h262, h363, h421, h422, h424, hc01, hlam, hphi, u1elo1]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h426 | h426
                                  · linarith only [h0, h187, h262, h419, h421, h422, h426, hc01, hc34, hlam, hphi, ht23, u1elo1, u2ehi3]
                                  · rcases h5bigk with h428c | h428c | h428c | h428c | h428c | h428c | h428c | h428c | h428c | h428c | h428c | h428c | h428c | h428c | h428c | h428c | h428c | h428c | h428c | h428c | h428c | h428c | h428c | h428c | h428c
                                    · have p428_0 := h428c.1
                                      have p428_1 := h428c.2.1
                                      have p428_2 := h428c.2.2.1
                                      have p428_3 := h428c.2.2.2
                                      linarith only [hlam, p428_0]
                                    · have p428_0 := h428c.1
                                      have p428_1 := h428c.2.1
                                      have p428_2 := h428c.2.2.1
                                      have p428_3 := h428c.2.2.2
                                      linarith only [h243, hlam, p428_1]
                                    · have p428_0 := h428c.1
                                      have p428_1 := h428c.2.1
                                      have p428_2 := h428c.2.2.1
                                      have p428_3 := h428c.2.2.2
                                      linarith only [h421, h422, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p428_1, u2ehi3]
                                    · have p428_0 := h428c.1
                                      have p428_1 := h428c.2.1
                                      have p428_2 := h428c.2.2.1
                                      have p428_3 := h428c.2.2.2
                                      linarith only [h263, hlam, p428_0]
                                    · have p428_0 := h428c.1
                                      have p428_1 := h428c.2.1
                                      have p428_2 := h428c.2.2.1
                                      have p428_3 := h428c.2.2.2
                                      linarith only [h363, hlam, p428_0]
                                    · have p428_0 := h428c.1
                                      have p428_1 := h428c.2.1
                                      have p428_2 := h428c.2.2.1
                                      have p428_3 := h428c.2.2.2
                                      linarith only [hc05, hlam, hphi, ht01, ht0b, ht5b, p428_1, u1elo4]
                                    · have p428_0 := h428c.1
                                      have p428_1 := h428c.2.1
                                      have p428_2 := h428c.2.2.1
                                      have p428_3 := h428c.2.2.2
                                      linarith only [hlam, p428_0]
                                    · have p428_0 := h428c.1
                                      have p428_1 := h428c.2.1
                                      have p428_2 := h428c.2.2.1
                                      have p428_3 := h428c.2.2.2
                                      linarith only [h416, h421, h422, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p428_1, u1elo1, u2ehi3]
                                    · have p428_0 := h428c.1
                                      have p428_1 := h428c.2.1
                                      have p428_2 := h428c.2.2.1
                                      have p428_3 := h428c.2.2.2
                                      linarith only [h417, hlam, p428_0]
                                    · have p428_0 := h428c.1
                                      have p428_1 := h428c.2.1
                                      have p428_2 := h428c.2.2.1
                                      have p428_3 := h428c.2.2.2
                                      linarith only [h419, hlam, p428_0]
                                    · have p428_0 := h428c.1
                                      have p428_1 := h428c.2.1
                                      have p428_2 := h428c.2.2.1
                                      have p428_3 := h428c.2.2.2
                                      linarith only [h262, hlam, p428_1]
                                    · have p428_0 := h428c.1
                                      have p428_1 := h428c.2.1
                                      have p428_2 := h428c.2.2.1
                                      have p428_3 := h428c.2.2.2
                                      linarith only [h416, hlam, p428_1]
                                    · have p428_0 := h428c.1
                                      have p428_1 := h428c.2.1
                                      have p428_2 := h428c.2.2.1
                                      have p428_3 := h428c.2.2.2
                                      linarith only [hlam, p428_0]
                                    · have p428_0 := h428c.1
                                      have p428_1 := h428c.2.1
                                      have p428_2 := h428c.2.2.1
                                      have p428_3 := h428c.2.2.2
                                      linarith only [h422, hlam, p428_1]
                                    · have p428_0 := h428c.1
                                      have p428_1 := h428c.2.1
                                      have p428_2 := h428c.2.2.1
                                      have p428_3 := h428c.2.2.2
                                      linarith only [h424, hlam, p428_0]
                                    · have p428_0 := h428c.1
                                      have p428_1 := h428c.2.1
                                      have p428_2 := h428c.2.2.1
                                      have p428_3 := h428c.2.2.2
                                      linarith only [h262, h421, h422, hc35, hlam, hphi, ht23, p428_1, u2ehi3]
                                    · have p428_0 := h428c.1
                                      have p428_1 := h428c.2.1
                                      have p428_2 := h428c.2.2.1
                                      have p428_3 := h428c.2.2.2
                                      linarith only [h243, h426, hc01, hc45, hlam, hphi, ht12, ht23, ht34, p428_1]
                                    · have p428_0 := h428c.1
                                      have p428_1 := h428c.2.1
                                      have p428_2 := h428c.2.2.1
                                      have p428_3 := h428c.2.2.2
                                      linarith only [h421, h422, h426, hc45, hlam, hphi, ht23, ht34, p428_1, u2ehi3]
                                    · have p428_0 := h428c.1
                                      have p428_1 := h428c.2.1
                                      have p428_2 := h428c.2.2.1
                                      have p428_3 := h428c.2.2.2
                                      linarith only [hlam, p428_0]
                                    · have p428_0 := h428c.1
                                      have p428_1 := h428c.2.1
                                      have p428_2 := h428c.2.2.1
                                      have p428_3 := h428c.2.2.2
                                      linarith only [h426, hlam, p428_0]
                                    · have p428_0 := h428c.1
                                      have p428_1 := h428c.2.1
                                      have p428_2 := h428c.2.2.1
                                      have p428_3 := h428c.2.2.2
                                      linarith only [h262, h421, h422, hc45, hlam, hphi, ht23, ht34, p428_1, u2ehi3]
                                    · have p428_0 := h428c.1
                                      have p428_1 := h428c.2.1
                                      have p428_2 := h428c.2.2.1
                                      have p428_3 := h428c.2.2.2
                                      linarith only [h0, h125, h262, h417, h421, h422, hc01, hc45, hlam, hphi, ht23, ht34, p428_1, u1elo1, u2ehi3]
                                    · have p428_0 := h428c.1
                                      have p428_1 := h428c.2.1
                                      have p428_2 := h428c.2.2.1
                                      have p428_3 := h428c.2.2.2
                                      linarith only [h421, h422, hc45, hlam, hphi, ht23, ht34, p428_1, u2ehi3]
                                    · have p428_0 := h428c.1
                                      have p428_1 := h428c.2.1
                                      have p428_2 := h428c.2.2.1
                                      have p428_3 := h428c.2.2.2
                                      linarith only [h263, hc03, hc45, hlam, hphi, ht34, p428_1]
                                    · have p428_0 := h428c.1
                                      have p428_1 := h428c.2.1
                                      have p428_2 := h428c.2.2.1
                                      have p428_3 := h428c.2.2.2
                                      linarith only [hlam, p428_0]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h454 | h454
                              · linarith only [h125, h417, h454, hc01, hc23, hlam, hphi, ht12]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h456 | h456
                                · linarith only [h187, h363, h415, h456, hc01, hlam, hphi, u1elo1]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h458 | h458
                                  · linarith only [h0, h187, h262, h419, h421, h456, h458, hc01, hc34, hlam, hphi, ht23, u1elo1, u2ehi2]
                                  · linarith only [h421, h458, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                      · linarith only [h0, h262, h416, hlam]
                    · linarith only [h0, h262, h415, hc24, hlam, hphi, u2ehi4]
                  · linarith only [h0, h262, h414, hc23, hlam, hphi, u2ehi4]
            · linarith only [h261, h262, hc25, hlam, hphi, u2ehi2]
          · rcases m.htr 0 2 5 (by decide) (by decide) with h465 | h465
            · linarith only [h261, h465, hc23, hlam, hphi, u2ehi4]
            · rcases m.htr 0 3 5 (by decide) (by decide) with h467 | h467
              · rcases m.htr 0 4 5 (by decide) (by decide) with h468 | h468
                · rcases m.htr 1 2 3 (by decide) (by decide) with h469 | h469
                  · linarith only [h261, h469, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo1, u2ehi0]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h471 | h471
                    · linarith only [h469, h471, hc23, hlam, hphi, u2ehi3]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h473 | h473
                      · linarith only [h469, h473, hc23, hlam, hphi, u2ehi4]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h475 | h475
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h476 | h476
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h477 | h477
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h478 | h478
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h479 | h479
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h480 | h480
                                  · rcases h5bigk with h481c | h481c | h481c | h481c | h481c | h481c | h481c | h481c | h481c | h481c | h481c | h481c | h481c | h481c | h481c | h481c | h481c | h481c | h481c | h481c | h481c | h481c | h481c | h481c | h481c
                                    · have p481_0 := h481c.1
                                      have p481_1 := h481c.2.1
                                      have p481_2 := h481c.2.2.1
                                      have p481_3 := h481c.2.2.2
                                      linarith only [hlam, p481_0]
                                    · have p481_0 := h481c.1
                                      have p481_1 := h481c.2.1
                                      have p481_2 := h481c.2.2.1
                                      have p481_3 := h481c.2.2.2
                                      linarith only [h243, hlam, p481_1]
                                    · have p481_0 := h481c.1
                                      have p481_1 := h481c.2.1
                                      have p481_2 := h481c.2.2.1
                                      have p481_3 := h481c.2.2.2
                                      linarith only [h465, hlam, p481_0]
                                    · have p481_0 := h481c.1
                                      have p481_1 := h481c.2.1
                                      have p481_2 := h481c.2.2.1
                                      have p481_3 := h481c.2.2.2
                                      linarith only [h187, h468, hc35, hlam, hphi, ht01, ht0b, ht5b, p481_1, u1elo3]
                                    · have p481_0 := h481c.1
                                      have p481_1 := h481c.2.1
                                      have p481_2 := h481c.2.2.1
                                      have p481_3 := h481c.2.2.2
                                      linarith only [h187, h468, hc45, hlam, hphi, ht01, ht0b, ht5b, p481_1, u1elo3]
                                    · have p481_0 := h481c.1
                                      have p481_1 := h481c.2.1
                                      have p481_2 := h481c.2.2.1
                                      have p481_3 := h481c.2.2.2
                                      linarith only [h475, hc05, hlam, hphi, ht01, ht0b, ht5b, p481_1, u1elo2]
                                    · have p481_0 := h481c.1
                                      have p481_1 := h481c.2.1
                                      have p481_2 := h481c.2.2.1
                                      have p481_3 := h481c.2.2.2
                                      linarith only [hlam, p481_0]
                                    · have p481_0 := h481c.1
                                      have p481_1 := h481c.2.1
                                      have p481_2 := h481c.2.2.1
                                      have p481_3 := h481c.2.2.2
                                      linarith only [h473, hlam, p481_0]
                                    · have p481_0 := h481c.1
                                      have p481_1 := h481c.2.1
                                      have p481_2 := h481c.2.2.1
                                      have p481_3 := h481c.2.2.2
                                      linarith only [h475, hc35, hlam, hphi, ht01, ht0b, ht5b, p481_1, u1elo2]
                                    · have p481_0 := h481c.1
                                      have p481_1 := h481c.2.1
                                      have p481_2 := h481c.2.2.1
                                      have p481_3 := h481c.2.2.2
                                      linarith only [h475, hc45, hlam, hphi, ht01, ht0b, ht5b, p481_1, u1elo2]
                                    · have p481_0 := h481c.1
                                      have p481_1 := h481c.2.1
                                      have p481_2 := h481c.2.2.1
                                      have p481_3 := h481c.2.2.2
                                      linarith only [h465, h477, h479, hc23, hlam, hphi, p481_1, u2ehi0]
                                    · have p481_0 := h481c.1
                                      have p481_1 := h481c.2.1
                                      have p481_2 := h481c.2.2.1
                                      have p481_3 := h481c.2.2.2
                                      linarith only [h243, h477, h479, hc01, hc23, hlam, hphi, ht12, p481_1]
                                    · have p481_0 := h481c.1
                                      have p481_1 := h481c.2.1
                                      have p481_2 := h481c.2.2.1
                                      have p481_3 := h481c.2.2.2
                                      linarith only [hlam, p481_0]
                                    · have p481_0 := h481c.1
                                      have p481_1 := h481c.2.1
                                      have p481_2 := h481c.2.2.1
                                      have p481_3 := h481c.2.2.2
                                      rcases p481_3 (m.d 0 5) (by simp) with h495 | h495
                                      · linarith only [h465, h495, hlam]
                                      · linarith only [h467, h495, hlam]
                                    · have p481_0 := h481c.1
                                      have p481_1 := h481c.2.1
                                      have p481_2 := h481c.2.2.1
                                      have p481_3 := h481c.2.2.2
                                      rcases p481_3 (m.d 0 5) (by simp) with h498 | h498
                                      · linarith only [h465, h498, hlam]
                                      · linarith only [h468, h498, hlam]
                                    · have p481_0 := h481c.1
                                      have p481_1 := h481c.2.1
                                      have p481_2 := h481c.2.2.1
                                      have p481_3 := h481c.2.2.2
                                      linarith only [h467, hlam, p481_1]
                                    · have p481_0 := h481c.1
                                      have p481_1 := h481c.2.1
                                      have p481_2 := h481c.2.2.1
                                      have p481_3 := h481c.2.2.2
                                      linarith only [h475, hlam, p481_1]
                                    · have p481_0 := h481c.1
                                      have p481_1 := h481c.2.1
                                      have p481_2 := h481c.2.2.1
                                      have p481_3 := h481c.2.2.2
                                      linarith only [h478, hlam, p481_0]
                                    · have p481_0 := h481c.1
                                      have p481_1 := h481c.2.1
                                      have p481_2 := h481c.2.2.1
                                      have p481_3 := h481c.2.2.2
                                      linarith only [hlam, p481_0]
                                    · have p481_0 := h481c.1
                                      have p481_1 := h481c.2.1
                                      have p481_2 := h481c.2.2.1
                                      have p481_3 := h481c.2.2.2
                                      linarith only [h125, h467, hc45, hlam, hphi, ht01, ht0b, ht5b, p481_1, u1elo2]
                                    · have p481_0 := h481c.1
                                      have p481_1 := h481c.2.1
                                      have p481_2 := h481c.2.2.1
                                      have p481_3 := h481c.2.2.2
                                      linarith only [h468, hlam, p481_1]
                                    · have p481_0 := h481c.1
                                      have p481_1 := h481c.2.1
                                      have p481_2 := h481c.2.2.1
                                      have p481_3 := h481c.2.2.2
                                      linarith only [h476, hlam, p481_1]
                                    · have p481_0 := h481c.1
                                      have p481_1 := h481c.2.1
                                      have p481_2 := h481c.2.2.1
                                      have p481_3 := h481c.2.2.2
                                      linarith only [h479, hlam, p481_1]
                                    · have p481_0 := h481c.1
                                      have p481_1 := h481c.2.1
                                      have p481_2 := h481c.2.2.1
                                      have p481_3 := h481c.2.2.2
                                      linarith only [h480, hlam, p481_1]
                                    · have p481_0 := h481c.1
                                      have p481_1 := h481c.2.1
                                      have p481_2 := h481c.2.2.1
                                      have p481_3 := h481c.2.2.2
                                      linarith only [hlam, p481_0]
                                  · rcases h5bigk with h511c | h511c | h511c | h511c | h511c | h511c | h511c | h511c | h511c | h511c | h511c | h511c | h511c | h511c | h511c | h511c | h511c | h511c | h511c | h511c | h511c | h511c | h511c | h511c | h511c
                                    · have p511_0 := h511c.1
                                      have p511_1 := h511c.2.1
                                      have p511_2 := h511c.2.2.1
                                      have p511_3 := h511c.2.2.2
                                      linarith only [hlam, p511_0]
                                    · have p511_0 := h511c.1
                                      have p511_1 := h511c.2.1
                                      have p511_2 := h511c.2.2.1
                                      have p511_3 := h511c.2.2.2
                                      linarith only [h243, hlam, p511_1]
                                    · have p511_0 := h511c.1
                                      have p511_1 := h511c.2.1
                                      have p511_2 := h511c.2.2.1
                                      have p511_3 := h511c.2.2.2
                                      linarith only [h465, hlam, p511_0]
                                    · have p511_0 := h511c.1
                                      have p511_1 := h511c.2.1
                                      have p511_2 := h511c.2.2.1
                                      have p511_3 := h511c.2.2.2
                                      linarith only [h243, hc35, hlam, hphi, ht01, ht0b, ht5b, p511_1, u1elo4]
                                    · have p511_0 := h511c.1
                                      have p511_1 := h511c.2.1
                                      have p511_2 := h511c.2.2.1
                                      have p511_3 := h511c.2.2.2
                                      linarith only [h125, h467, h480, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p511_1, u1elo2]
                                    · have p511_0 := h511c.1
                                      have p511_1 := h511c.2.1
                                      have p511_2 := h511c.2.2.1
                                      have p511_3 := h511c.2.2.2
                                      linarith only [hc05, hlam, hphi, ht01, ht0b, ht5b, p511_1, u1elo4]
                                    · have p511_0 := h511c.1
                                      have p511_1 := h511c.2.1
                                      have p511_2 := h511c.2.2.1
                                      have p511_3 := h511c.2.2.2
                                      linarith only [hlam, p511_0]
                                    · have p511_0 := h511c.1
                                      have p511_1 := h511c.2.1
                                      have p511_2 := h511c.2.2.1
                                      have p511_3 := h511c.2.2.2
                                      linarith only [h473, hlam, p511_0]
                                    · have p511_0 := h511c.1
                                      have p511_1 := h511c.2.1
                                      have p511_2 := h511c.2.2.1
                                      have p511_3 := h511c.2.2.2
                                      linarith only [h475, hc35, hlam, hphi, ht01, ht0b, ht5b, p511_1, u1elo2]
                                    · have p511_0 := h511c.1
                                      have p511_1 := h511c.2.1
                                      have p511_2 := h511c.2.2.1
                                      have p511_3 := h511c.2.2.2
                                      linarith only [h475, h480, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p511_1, u1elo2]
                                    · have p511_0 := h511c.1
                                      have p511_1 := h511c.2.1
                                      have p511_2 := h511c.2.2.1
                                      have p511_3 := h511c.2.2.2
                                      linarith only [h465, h477, h479, hc23, hlam, hphi, p511_1, u2ehi0]
                                    · have p511_0 := h511c.1
                                      have p511_1 := h511c.2.1
                                      have p511_2 := h511c.2.2.1
                                      have p511_3 := h511c.2.2.2
                                      linarith only [h243, h477, h479, hc01, hc23, hlam, hphi, ht12, p511_1]
                                    · have p511_0 := h511c.1
                                      have p511_1 := h511c.2.1
                                      have p511_2 := h511c.2.2.1
                                      have p511_3 := h511c.2.2.2
                                      linarith only [hlam, p511_0]
                                    · have p511_0 := h511c.1
                                      have p511_1 := h511c.2.1
                                      have p511_2 := h511c.2.2.1
                                      have p511_3 := h511c.2.2.2
                                      rcases p511_3 (m.d 0 5) (by simp) with h525 | h525
                                      · linarith only [h465, h525, hlam]
                                      · linarith only [h467, h525, hlam]
                                    · have p511_0 := h511c.1
                                      have p511_1 := h511c.2.1
                                      have p511_2 := h511c.2.2.1
                                      have p511_3 := h511c.2.2.2
                                      linarith only [h477, h479, h480, hc23, hc34, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, p511_1]
                                    · have p511_0 := h511c.1
                                      have p511_1 := h511c.2.1
                                      have p511_2 := h511c.2.2.1
                                      have p511_3 := h511c.2.2.2
                                      linarith only [h467, hlam, p511_1]
                                    · have p511_0 := h511c.1
                                      have p511_1 := h511c.2.1
                                      have p511_2 := h511c.2.2.1
                                      have p511_3 := h511c.2.2.2
                                      linarith only [h475, hlam, p511_1]
                                    · have p511_0 := h511c.1
                                      have p511_1 := h511c.2.1
                                      have p511_2 := h511c.2.2.1
                                      have p511_3 := h511c.2.2.2
                                      linarith only [h478, hlam, p511_0]
                                    · have p511_0 := h511c.1
                                      have p511_1 := h511c.2.1
                                      have p511_2 := h511c.2.2.1
                                      have p511_3 := h511c.2.2.2
                                      linarith only [hlam, p511_0]
                                    · have p511_0 := h511c.1
                                      have p511_1 := h511c.2.1
                                      have p511_2 := h511c.2.2.1
                                      have p511_3 := h511c.2.2.2
                                      linarith only [h480, hlam, p511_0]
                                    · have p511_0 := h511c.1
                                      have p511_1 := h511c.2.1
                                      have p511_2 := h511c.2.2.1
                                      have p511_3 := h511c.2.2.2
                                      linarith only [h468, hlam, p511_1]
                                    · have p511_0 := h511c.1
                                      have p511_1 := h511c.2.1
                                      have p511_2 := h511c.2.2.1
                                      have p511_3 := h511c.2.2.2
                                      linarith only [h476, hlam, p511_1]
                                    · have p511_0 := h511c.1
                                      have p511_1 := h511c.2.1
                                      have p511_2 := h511c.2.2.1
                                      have p511_3 := h511c.2.2.2
                                      linarith only [h479, hlam, p511_1]
                                    · have p511_0 := h511c.1
                                      have p511_1 := h511c.2.1
                                      have p511_2 := h511c.2.2.1
                                      have p511_3 := h511c.2.2.2
                                      linarith only [h480, hc34, hc45, hlam, hphi, p511_1]
                                    · have p511_0 := h511c.1
                                      have p511_1 := h511c.2.1
                                      have p511_2 := h511c.2.2.1
                                      have p511_3 := h511c.2.2.2
                                      linarith only [hlam, p511_0]
                                · linarith only [h187, h468, h479, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo3, u2ehi3]
                              · linarith only [h0, h471, h477, h478, hc01, hc35, hlam, hphi, ht12, ht23]
                            · linarith only [h261, h477, hc34, hlam, hphi, ht23, u2ehi0]
                          · linarith only [h187, h468, h476, hlam]
                        · linarith only [h125, h467, h475, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h544 | h544
                  · linarith only [h261, h544, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo1, u2ehi0]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h546 | h546
                    · linarith only [h544, h546, hc23, hlam, hphi, u2ehi3]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h548 | h548
                      · linarith only [h544, h548, hc23, hlam, hphi, u2ehi4]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h550 | h550
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h551 | h551
                          · linarith only [h187, h468, h551, hc01, hlam, hphi, u1elo3]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h553 | h553
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h554 | h554
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h555 | h555
                                · linarith only [h546, h551, h555, hc24, hlam, hphi, u2ehi1]
                                · linarith only [h0, h546, h555, hc01, hc45, hlam, hphi, ht12, ht23, ht34]
                              · linarith only [h125, h467, h553, h554, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, u1elo2]
                            · linarith only [h0, h544, h553, hc01, hc34, hlam, hphi, ht12, ht23]
                        · linarith only [h125, h467, h550, hlam]
              · rcases m.htr 0 4 5 (by decide) (by decide) with h561 | h561
                · rcases m.htr 1 2 3 (by decide) (by decide) with h562 | h562
                  · linarith only [h261, h562, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo1, u2ehi0]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h564 | h564
                    · linarith only [h562, h564, hc23, hlam, hphi, u2ehi3]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h566 | h566
                      · linarith only [h562, h566, hc23, hlam, hphi, u2ehi4]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h568 | h568
                        · linarith only [h261, h467, h568, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2, u2ehi0]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h570 | h570
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h571 | h571
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h572 | h572
                              · linarith only [h562, h568, h572, hc23, hlam, hphi, u2ehi1]
                              · linarith only [h261, h572, hc35, hlam, hphi, ht23, u2ehi0]
                            · linarith only [h0, h562, h571, hc01, hc34, hlam, hphi, ht12, ht23]
                          · linarith only [h187, h561, h570, hlam]
                · rcases m.htr 1 2 3 (by decide) (by decide) with h577 | h577
                  · linarith only [h261, h577, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo1, u2ehi0]
                  · rcases m.htr 1 2 4 (by decide) (by decide) with h579 | h579
                    · linarith only [h577, h579, hc23, hlam, hphi, u2ehi3]
                    · rcases m.htr 1 2 5 (by decide) (by decide) with h581 | h581
                      · linarith only [h577, h581, hc23, hlam, hphi, u2ehi4]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h583 | h583
                        · linarith only [h261, h467, h583, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u1elo2, u2ehi0]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h585 | h585
                          · linarith only [h187, h561, h585, hc01, hlam, hphi, u1elo3]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h587 | h587
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h588 | h588
                              · linarith only [h125, h583, h588, hc01, hc23, hlam, hphi, ht12]
                              · linarith only [h261, h588, hc35, hlam, hphi, ht23, u2ehi0]
                            · linarith only [h577, h587, hc34, hlam, hphi, ht23, u2ehi1]

end R2N4
