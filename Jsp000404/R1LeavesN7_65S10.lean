import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_20_11_13_14_M_LR_L_I_L_I_L_R (m : N7Model)
    (hb0 : CMSig2_7_M_LR m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_R m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h4ehi := hb4.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  have u0ehi5 := h0ehi (m.d 0 1) (by simp)
  have u0ehi6 := h0ehi (m.d 0 2) (by simp)
  have u0ehi7 := h0ehi (m.d 0 3) (by simp)
  have u0ehi8 := h0ehi (m.d 0 4) (by simp)
  have u0ehi9 := h0ehi (m.d 0 5) (by simp)
  have u4ehi0 := h4ehi (m.d 0 4) (by simp)
  have u4ehi1 := h4ehi (m.d 1 4) (by simp)
  have u4ehi2 := h4ehi (m.d 2 4) (by simp)
  have u4ehi3 := h4ehi (m.d 3 4) (by simp)
  have u4ehi4 := h4ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 2 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 2 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 0 3 4 (by decide) (by decide) with h7 | h7
                · rcases m.htr 0 4 5 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h10 | h10
                      · linarith only [h0, h10, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi2]
                      · linarith only [h0, h10, h5, h9, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h13 | h13
                      · linarith only [h0, h13, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi2]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h15 | h15
                        · linarith only [h0, h15, h4, h9, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h17 | h17
                          · linarith only [h1, h17, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi3]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h19 | h19
                            · linarith only [h0, h17, h19, h4, h7, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h21 | h21
                              · linarith only [h2, h21, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi4]
                              · linarith only [h0, h21, h4, h7, h8, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h24 | h24
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h25 | h25
                      · linarith only [h0, h25, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi2]
                      · linarith only [h0, h24, h25, h5, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h28 | h28
                      · linarith only [h0, h28, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi2]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h30 | h30
                        · linarith only [h0, h24, h30, h4, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h32 | h32
                          · linarith only [h1, h32, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi3]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h34 | h34
                            · linarith only [h0, h32, h34, h4, h7, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h36 | h36
                              · linarith only [h36, h8, hc14, hlam, hphi, ht01, u0ehi8]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h38 | h38
                                · linarith only [h0, h24, h32, h38, h4, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                                · linarith only [h0, h24, h38, h4, h7, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h41 | h41
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h42 | h42
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h43 | h43
                      · linarith only [h0, h43, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi2]
                      · linarith only [h0, h42, h43, h5, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h46 | h46
                      · linarith only [h0, h46, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi2]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h48 | h48
                        · linarith only [h0, h4, h42, h48, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h50 | h50
                          · linarith only [h0, h4, h42, h50, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi3]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h52 | h52
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h53 | h53
                              · linarith only [h0, h46, h5, h53, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi4]
                              · linarith only [h41, h53, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi1]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h56 | h56
                              · linarith only [h2, h56, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi4]
                              · linarith only [h0, h41, h5, h56, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h59 | h59
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h60 | h60
                      · linarith only [h0, h60, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi2]
                      · linarith only [h0, h5, h59, h60, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h63 | h63
                      · linarith only [h0, h63, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi2]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h65 | h65
                        · linarith only [h0, h4, h59, h65, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h67 | h67
                          · linarith only [h67, h7, hc13, hlam, hphi, ht01, u0ehi7]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h69 | h69
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h70 | h70
                              · linarith only [h41, h70, hc14, hlam, hphi, ht01, u0ehi8]
                              · linarith only [h67, h69, h70, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h73 | h73
                              · linarith only [h0, h41, h5, h63, h7, h73, hlam, hphi, u0ehi7, u0elo0]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h75 | h75
                                · linarith only [h0, h4, h7, h75, hlam, hphi, u0ehi7, u0elo0]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h77 | h77
                                  · linarith only [h0, h5, h69, h75, h77, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h79 | h79
                                    · linarith only [h0, h41, h5, h7, h79, hlam, hphi, u0ehi7, u0elo0]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h81 | h81
                                      · linarith only [h41, h7, h81, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi7]
                                      · linarith only [h0, h59, h6, h7, h75, h79, h81, hc12, hc45, hlam, hphi, ht23, ht34, u0ehi7, u0elo0]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h84 | h84
                · rcases m.htr 0 4 5 (by decide) (by decide) with h85 | h85
                  · linarith only [h4, h6, h84, h85, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h87 | h87
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h88 | h88
                      · linarith only [h0, h88, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi2]
                      · linarith only [h5, h6, h88, hc12, hc25, hlam, hphi]
                    · linarith only [h4, h6, h87, hc12, hc25, hlam, hphi]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h92 | h92
                  · linarith only [h5, h6, h92, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h94 | h94
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h95 | h95
                      · linarith only [h0, h95, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi2]
                      · linarith only [h5, h6, h95, hc12, hc25, hlam, hphi]
                    · linarith only [h4, h6, h94, hc12, hc25, hlam, hphi]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h99 | h99
              · rcases m.htr 0 3 4 (by decide) (by decide) with h100 | h100
                · linarith only [h100, h4, h5, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h102 | h102
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h103 | h103
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h104 | h104
                      · linarith only [h104, h5, hc12, hlam, hphi, ht01, u0ehi6]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h106 | h106
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h107 | h107
                          · linarith only [h1, h107, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi3]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h109 | h109
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h110 | h110
                              · linarith only [h110, h2, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi4]
                              · linarith only [h102, h110, h2, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi1]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h113 | h113
                              · linarith only [h113, h2, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi4]
                              · linarith only [h102, h113, h2, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi1]
                        · linarith only [h103, h106, h99, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h103, h4, h5, hc12, hc24, hlam, hphi]
                  · linarith only [h102, h5, h99, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h119 | h119
                · linarith only [h119, h4, h5, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h121 | h121
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h122 | h122
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h123 | h123
                      · linarith only [h0, h123, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi2]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h125 | h125
                        · linarith only [h123, h125, h2, h99, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h127 | h127
                          · linarith only [h119, h127, hc13, hlam, hphi, ht01, u0ehi7]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h129 | h129
                            · linarith only [h122, h125, h129, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h131 | h131
                              · linarith only [h131, h2, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi4]
                              · linarith only [h121, h131, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi1]
                    · linarith only [h122, h4, h5, hc12, hc24, hlam, hphi]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h135 | h135
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h136 | h136
                      · linarith only [h136, h4, h5, hc12, hlam, hphi, ht01, u0ehi7]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h138 | h138
                        · linarith only [h136, h138, h2, h4, h99, hlam, hphi, u0ehi7, u0elo0]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h140 | h140
                          · linarith only [h119, h140, hc13, hlam, hphi, ht01, u0ehi7]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h142 | h142
                            · linarith only [h135, h138, h142, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h144 | h144
                              · linarith only [h121, h144, h2, h4, h5, hlam, hphi, u0ehi7, u0elo0]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h146 | h146
                                · linarith only [h119, h146, hc23, hlam, hphi, ht01, ht12, u0ehi7]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h148 | h148
                                  · linarith only [h121, h135, h136, h142, h144, h148, h3, h4, h5, hc13, hc45, hlam, hphi, ht34, u0ehi7, u0elo0]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h150 | h150
                                    · linarith only [h121, h150, h4, h5, hc24, hlam, hphi, ht01, ht12, u0ehi7]
                                    · linarith only [h150, h4, h5, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi7]
                    · linarith only [h135, h4, h5, hc12, hc24, hlam, hphi]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h154 | h154
            · rcases m.htr 0 2 5 (by decide) (by decide) with h155 | h155
              · rcases m.htr 0 3 4 (by decide) (by decide) with h156 | h156
                · rcases m.htr 0 4 5 (by decide) (by decide) with h157 | h157
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h158 | h158
                    · linarith only [h154, h158, h4, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h160 | h160
                      · linarith only [h0, h160, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi2]
                      · linarith only [h154, h160, h4, hc12, hc23, hlam, hphi]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h163 | h163
                    · linarith only [h154, h163, h4, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h165 | h165
                      · linarith only [h1, h163, h165, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi2]
                      · linarith only [h154, h165, h4, hc12, hc23, hlam, hphi]
                · linarith only [h154, h156, h4, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h169 | h169
                · rcases m.htr 0 4 5 (by decide) (by decide) with h170 | h170
                  · linarith only [h154, h155, h170, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h172 | h172
                    · linarith only [h172, h4, hc12, hlam, hphi, ht01, u0ehi6]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h174 | h174
                      · linarith only [h1, h172, h174, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi2]
                      · linarith only [h154, h174, h4, hc12, hc23, hlam, hphi]
                · linarith only [h154, h169, h4, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h178 | h178
              · rcases m.htr 0 3 4 (by decide) (by decide) with h179 | h179
                · rcases m.htr 0 4 5 (by decide) (by decide) with h180 | h180
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h181 | h181
                    · linarith only [h0, h181, h4, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h183 | h183
                      · linarith only [h1, h181, h183, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi2]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h185 | h185
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h186 | h186
                          · linarith only [h1, h186, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi3]
                          · linarith only [h1, h179, h181, h185, h186, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                        · linarith only [h178, h185, h4, hc12, hc23, hlam, hphi]
                  · linarith only [h154, h178, h180, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h191 | h191
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h192 | h192
                    · linarith only [h178, h192, h4, hc12, hlam, hphi, ht01, u0ehi9]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h194 | h194
                      · linarith only [h1, h154, h178, h192, h194, hlam, hphi, u0ehi9, u0elo0]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h196 | h196
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h197 | h197
                          · linarith only [h1, h197, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi3]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h199 | h199
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h200 | h200
                              · linarith only [h2, h200, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi4]
                              · linarith only [h191, h200, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi1]
                            · linarith only [h192, h196, h199, hlam]
                        · linarith only [h178, h196, h4, hc12, hc23, hlam, hphi]
                  · linarith only [h154, h178, h191, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h206 | h206
                · rcases m.htr 0 4 5 (by decide) (by decide) with h207 | h207
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h208 | h208
                    · linarith only [h208, h4, hc12, hlam, hphi, ht01, u0ehi6]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h210 | h210
                      · linarith only [h154, h210, hc12, hlam, hphi, ht01, u0ehi6]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h212 | h212
                        · linarith only [h1, h178, h208, h212, hlam, hphi, u0ehi6, u0elo0]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h214 | h214
                          · linarith only [h1, h214, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi3]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h216 | h216
                            · linarith only [h206, h214, h216, hc35, hlam, hphi, ht0b, ht5b, u0elo2]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h218 | h218
                              · linarith only [h2, h218, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi4]
                              · linarith only [h1, h206, h207, h218, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h221 | h221
                    · linarith only [h221, h4, hc12, hlam, hphi, ht01, u0ehi6]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h223 | h223
                      · linarith only [h154, h223, hc12, hlam, hphi, ht01, u0ehi6]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h225 | h225
                        · linarith only [h1, h178, h221, h225, hlam, hphi, u0ehi6, u0elo0]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h227 | h227
                          · linarith only [h1, h227, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi3]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h229 | h229
                            · linarith only [h1, h206, h227, h229, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h231 | h231
                              · linarith only [h207, h231, hc14, hlam, hphi, ht01, u0ehi8]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h233 | h233
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h234 | h234
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h235 | h235
                                    · linarith only [h1, h154, h206, h207, h221, h227, h233, h235, hc12, hc23, hlam, hphi, u0ehi6, u0elo0]
                                    · linarith only [h1, h154, h206, h221, h227, h235, hc12, hc45, hlam, hphi, ht23, ht34, u0ehi6, u0elo0]
                                  · linarith only [h1, h206, h221, h227, h234, h4, hc12, hc35, hlam, hphi, ht23, u0ehi6, u0elo0]
                                · linarith only [h1, h206, h233, h4, hlam, hphi, u0ehi6, u0elo0]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h240 | h240
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h241 | h241
                    · linarith only [h241, h4, hc12, hlam, hphi, ht01, u0ehi6]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h243 | h243
                      · linarith only [h154, h243, hc12, hlam, hphi, ht01, u0ehi6]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h245 | h245
                        · linarith only [h1, h178, h241, h245, hlam, hphi, u0ehi6, u0elo0]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h247 | h247
                          · linarith only [h1, h206, h247, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h249 | h249
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h250 | h250
                              · linarith only [h2, h250, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi4]
                              · linarith only [h240, h250, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi1]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h253 | h253
                              · linarith only [h2, h253, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi4]
                              · linarith only [h2, h240, h253, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h256 | h256
                    · linarith only [h256, h4, hc12, hlam, hphi, ht01, u0ehi6]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h258 | h258
                      · linarith only [h1, h154, h256, h258, hlam, hphi, u0ehi6, u0elo0]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h260 | h260
                        · linarith only [h1, h178, h256, h260, hlam, hphi, u0ehi6, u0elo0]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h262 | h262
                          · linarith only [h1, h206, h262, h4, hlam, hphi, u0ehi6, u0elo0]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h264 | h264
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h265 | h265
                              · linarith only [h2, h206, h240, h265, h4, hlam, hphi, u0ehi6, u0elo0]
                              · linarith only [h262, h264, h265, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h268 | h268
                              · linarith only [h2, h206, h240, h268, h4, hlam, hphi, u0ehi6, u0elo0]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h270 | h270
                                · linarith only [h206, h270, h4, hc23, hlam, hphi, ht01, ht12, u0ehi6]
                                · linarith only [h270, h4, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi6]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h273 | h273
          · rcases m.htr 0 2 4 (by decide) (by decide) with h274 | h274
            · rcases m.htr 0 2 5 (by decide) (by decide) with h275 | h275
              · linarith only [h0, h275, h3, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h277 | h277
                · rcases m.htr 0 4 5 (by decide) (by decide) with h278 | h278
                  · linarith only [h1, h277, h278, h3, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h280 | h280
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h281 | h281
                      · linarith only [h0, h281, h3, hc15, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                      · linarith only [h274, h275, h280, h281, hc23, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                    · linarith only [h273, h275, h280, hc12, hc25, hlam, hphi]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h285 | h285
                  · linarith only [h0, h274, h285, h3, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h287 | h287
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h288 | h288
                      · linarith only [h0, h288, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi2]
                      · linarith only [h274, h275, h288, hc12, hc25, hlam, hphi]
                    · linarith only [h273, h275, h287, hc12, hc25, hlam, hphi]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h292 | h292
              · linarith only [h2, h274, h292, h3, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h294 | h294
                · linarith only [h273, h274, h294, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h296 | h296
                  · linarith only [h2, h296, h3, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h298 | h298
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h299 | h299
                      · linarith only [h0, h274, h299, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h301 | h301
                        · linarith only [h2, h273, h292, h299, h3, h301, hlam, hphi, u0ehi7, u0elo4]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h303 | h303
                          · linarith only [h2, h294, h298, h299, h3, h301, h303, hc25, hlam, hphi, ht01, ht12, u0ehi7]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h305 | h305
                            · linarith only [h2, h298, h299, h3, h305, hlam]
                            · linarith only [h2, h298, h299, h3, h305, hc23, hc35, hlam, hphi]
                    · linarith only [h273, h274, h296, h298, hc12, hc45, hlam, hphi, ht23, ht34]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h309 | h309
            · rcases m.htr 0 2 5 (by decide) (by decide) with h310 | h310
              · linarith only [h1, h273, h3, h310, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h312 | h312
                · rcases m.htr 0 4 5 (by decide) (by decide) with h313 | h313
                  · linarith only [h1, h273, h3, h309, h313, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h315 | h315
                    · linarith only [h273, h315, hc12, hlam, hphi, ht01, u0ehi6]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h317 | h317
                      · linarith only [h1, h315, h317, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi2]
                      · linarith only [h273, h309, h317, hc12, hc23, hlam, hphi]
                · linarith only [h273, h309, h312, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h321 | h321
              · linarith only [h0, h3, h321, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h323 | h323
                · rcases m.htr 0 4 5 (by decide) (by decide) with h324 | h324
                  · linarith only [h1, h3, h323, h324, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h326 | h326
                    · linarith only [h0, h273, h326, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h328 | h328
                      · linarith only [h1, h3, h309, h326, h328, hlam, hphi, u0ehi6, u0elo4]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h330 | h330
                        · linarith only [h1, h3, h321, h326, h330, hlam, hphi, u0ehi6, u0elo4]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h332 | h332
                          · linarith only [h1, h3, h330, h332, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                          · linarith only [h1, h3, h323, h326, h330, h332, hc12, hc25, hlam, hphi]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h335 | h335
                  · linarith only [h2, h3, h335, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h337 | h337
                    · linarith only [h273, h337, hc12, hlam, hphi, ht01, u0ehi6]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h339 | h339
                      · linarith only [h1, h3, h309, h337, h339, hc15, hlam, hphi, ht01, u0ehi6]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h341 | h341
                        · linarith only [h1, h3, h321, h337, h341, hc15, hlam, hphi, ht01, u0ehi6]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h343 | h343
                          · linarith only [h1, h3, h341, h343, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h345 | h345
                            · linarith only [h2, h3, h343, h345, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h347 | h347
                              · linarith only [h2, h273, h3, h323, h335, h345, h347, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi6]
                              · linarith only [h2, h3, h347, hc45, hlam, hphi, u4ehi1]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h350 | h350
        · rcases m.htr 0 2 3 (by decide) (by decide) with h351 | h351
          · rcases m.htr 0 2 4 (by decide) (by decide) with h352 | h352
            · linarith only [h0, h2, h352, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h354 | h354
              · rcases m.htr 0 3 4 (by decide) (by decide) with h355 | h355
                · linarith only [h1, h2, h355, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h357 | h357
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h358 | h358
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h359 | h359
                      · linarith only [h0, h352, h359, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h361 | h361
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h362 | h362
                          · linarith only [h355, h362, hc13, hlam, hphi, ht01, u0ehi7]
                          · linarith only [h0, h2, h358, h362, hc23, hc34, hlam, hphi]
                        · linarith only [h354, h358, h361, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h351, h352, h358, hc12, hc24, hlam, hphi]
                  · linarith only [h2, h350, h357, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h368 | h368
                · linarith only [h0, h2, h351, h368, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h370 | h370
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h371 | h371
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h372 | h372
                      · linarith only [h0, h372, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi2]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h374 | h374
                        · linarith only [h0, h2, h354, h372, h374, hc02, hc24, hlam, hphi]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h376 | h376
                          · linarith only [h2, h350, h368, h371, h372, h374, h376, hc24, hlam, hphi, ht01, ht12, u0ehi7]
                          · linarith only [h2, h350, h371, h374, h376, hc23, hc34, hlam, hphi]
                    · linarith only [h351, h354, h371, hc12, hc25, hlam, hphi]
                  · linarith only [h2, h350, h370, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h381 | h381
            · linarith only [h1, h2, h351, h381, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h383 | h383
              · rcases m.htr 0 3 4 (by decide) (by decide) with h384 | h384
                · linarith only [h1, h2, h384, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h386 | h386
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h387 | h387
                    · linarith only [h351, h387, hc12, hlam, hphi, ht01, u0ehi6]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h389 | h389
                      · linarith only [h381, h383, h389, hc12, hlam, hphi, ht01, u0ehi9]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h391 | h391
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h392 | h392
                          · linarith only [h1, h2, h389, h392, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h394 | h394
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h395 | h395
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h396 | h396
                                · linarith only [h1, h2, h387, h392, h396, hc12, hc23, hlam, hphi]
                                · linarith only [h351, h383, h396, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi9]
                              · linarith only [h1, h2, h387, h395, hc12, hc45, hlam, hphi, ht23, ht34]
                            · linarith only [h387, h391, h394, hlam]
                        · linarith only [h351, h383, h391, hc12, hc23, hlam, hphi]
                  · linarith only [h2, h350, h386, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h403 | h403
                · linarith only [h1, h2, h403, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h405 | h405
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h406 | h406
                    · linarith only [h351, h406, hc12, hlam, hphi, ht01, u0ehi6]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h408 | h408
                      · linarith only [h1, h406, h408, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi2]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h410 | h410
                        · linarith only [h1, h2, h383, h406, h408, h410, hc24, hlam, hphi, ht01, ht12, u0ehi6]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h412 | h412
                          · linarith only [h1, h2, h403, h408, h412, hc03, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h414 | h414
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h415 | h415
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h416 | h416
                                · linarith only [h1, h2, h410, h412, h414, h416, hc12, hc23, hlam, hphi]
                                · linarith only [h351, h416, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi6]
                              · linarith only [h1, h2, h415, hc13, hc45, hlam, hphi, ht34]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h420 | h420
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h421 | h421
                                · linarith only [h351, h403, h421, hc23, hlam, hphi, ht01, ht12, u0ehi6]
                                · linarith only [h351, h421, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi6]
                              · linarith only [h2, h420, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi5]
                  · linarith only [h2, h350, h405, hlam]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h426 | h426
          · rcases m.htr 0 2 4 (by decide) (by decide) with h427 | h427
            · linarith only [h0, h2, h427, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h429 | h429
              · linarith only [h0, h350, h429, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h431 | h431
                · linarith only [h1, h2, h431, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h433 | h433
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h434 | h434
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h435 | h435
                      · linarith only [h0, h427, h435, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h437 | h437
                        · linarith only [h0, h2, h426, h429, h435, h437, hc24, hlam, hphi, ht01, ht12, u0ehi7]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h439 | h439
                          · linarith only [h431, h439, hc13, hlam, hphi, ht01, u0ehi7]
                          · linarith only [h0, h2, h434, h439, hc23, hc34, hlam, hphi]
                    · linarith only [h426, h427, h434, hc12, hc24, hlam, hphi]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h443 | h443
                    · linarith only [h0, h2, h433, h443, hc23, hc45, hlam, hphi, ht34]
                    · linarith only [h0, h2, h426, h433, h443, hc12, hc45, hlam, hphi, ht23, ht34]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h446 | h446
            · linarith only [h1, h2, h426, h446, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h448 | h448
              · linarith only [h1, h350, h426, h448, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h450 | h450
                · linarith only [h1, h2, h450, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h452 | h452
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h453 | h453
                    · linarith only [h426, h453, hc12, hlam, hphi, ht01, u0ehi6]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h455 | h455
                      · linarith only [h1, h350, h446, h452, h453, h455, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h457 | h457
                        · linarith only [h1, h2, h448, h453, h455, h457, hc02, hc24, hlam, hphi]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h459 | h459
                          · linarith only [h1, h2, h455, h459, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h461 | h461
                            · linarith only [h1, h350, h461, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h463 | h463
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h464 | h464
                                · linarith only [h1, h350, h453, h459, h463, h464, hc12, hc23, hlam, hphi]
                                · linarith only [h426, h464, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi6]
                              · linarith only [h452, h463, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h468 | h468
                    · linarith only [h426, h468, hc12, hlam, hphi, ht01, u0ehi6]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h470 | h470
                      · linarith only [h1, h468, h470, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi2]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h472 | h472
                        · linarith only [h1, h2, h448, h452, h468, h472, hc02, hc45, hlam, hphi, ht23, ht34]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h474 | h474
                          · linarith only [h1, h2, h452, h474, hc45, hlam, hphi, u4ehi3]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h476 | h476
                            · linarith only [h1, h350, h476, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h478 | h478
                              · linarith only [h1, h2, h452, h468, h470, h478, hc12, hc24, hlam, hphi]
                              · linarith only [h1, h2, h426, h478, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi6]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h481 | h481
      · rcases m.htr 0 1 5 (by decide) (by decide) with h482 | h482
        · rcases m.htr 0 2 3 (by decide) (by decide) with h483 | h483
          · linarith only [h0, h1, h483, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h485 | h485
            · rcases m.htr 0 2 5 (by decide) (by decide) with h486 | h486
              · rcases m.htr 0 3 4 (by decide) (by decide) with h487 | h487
                · rcases m.htr 0 4 5 (by decide) (by decide) with h488 | h488
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h489 | h489
                    · linarith only [h483, h485, h488, h489, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h491 | h491
                      · linarith only [h0, h491, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi2]
                      · linarith only [h0, h1, h485, h489, h491, hc12, hc23, hlam, hphi]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h494 | h494
                    · linarith only [h0, h1, h483, h494, hc02, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h496 | h496
                      · linarith only [h0, h1, h494, h496, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
                      · linarith only [h0, h1, h485, h494, h496, hc12, hc23, hlam, hphi]
                · linarith only [h1, h481, h487, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h500 | h500
                · rcases m.htr 0 4 5 (by decide) (by decide) with h501 | h501
                  · linarith only [h485, h486, h501, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h503 | h503
                    · linarith only [h0, h483, h503, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h505 | h505
                      · linarith only [h0, h1, h503, h505, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
                      · linarith only [h485, h486, h505, hc12, hc25, hlam, hphi]
                · linarith only [h1, h481, h500, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h509 | h509
              · rcases m.htr 0 3 4 (by decide) (by decide) with h510 | h510
                · rcases m.htr 0 4 5 (by decide) (by decide) with h511 | h511
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h512 | h512
                    · linarith only [h483, h512, hc12, hlam, hphi, ht01, u0ehi6]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h514 | h514
                      · linarith only [h0, h1, h485, h509, h512, h514, hc23, hlam, hphi, ht01, ht12, u0ehi9]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h516 | h516
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h517 | h517
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h518 | h518
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h519 | h519
                              · linarith only [h1, h481, h512, h519, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                              · linarith only [h1, h481, h511, h512, h514, h519, hc12, hc23, hlam, hphi]
                            · linarith only [h1, h518, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi5]
                          · linarith only [h1, h481, h511, h517, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
                        · linarith only [h485, h509, h516, hc12, hc24, hlam, hphi]
                  · linarith only [h485, h509, h511, hlam]
                · linarith only [h1, h481, h510, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h527 | h527
                · rcases m.htr 0 4 5 (by decide) (by decide) with h528 | h528
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h529 | h529
                    · linarith only [h483, h529, hc12, hlam, hphi, ht01, u0ehi6]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h531 | h531
                      · linarith only [h0, h485, h531, hlam, hphi, u0ehi6, u0elo0]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h533 | h533
                        · linarith only [h1, h481, h509, h529, h531, h533, hc23, hlam, hphi, ht01, ht12, u0ehi6]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h535 | h535
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h536 | h536
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h537 | h537
                              · linarith only [h1, h481, h529, h537, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                              · linarith only [h528, h537, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi1]
                            · linarith only [h1, h481, h531, h536, hc12, hc35, hlam, hphi, ht23]
                          · linarith only [h1, h481, h528, h535, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h542 | h542
                    · linarith only [h0, h483, h542, hlam, hphi, u0ehi6, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h544 | h544
                      · linarith only [h0, h1, h485, h542, h544, hc23, hlam, hphi, ht01, ht12, u0ehi6]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h546 | h546
                        · linarith only [h1, h481, h509, h542, h544, h546, hc23, hlam, hphi, ht01, ht12, u0ehi6]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h548 | h548
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h549 | h549
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h550 | h550
                              · linarith only [h1, h481, h528, h542, h550, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi0]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h552 | h552
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h553 | h553
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h554 | h554
                                    · linarith only [h485, h528, h554, hc24, hlam, hphi, ht01, ht12, u0ehi6]
                                    · linarith only [h1, h482, h485, h542, h548, h550, h554, hc23, hc45, hlam, hphi, ht01, ht12, u0ehi6, u4ehi3]
                                  · linarith only [h1, h482, h542, h549, h553, hlam]
                                · linarith only [h1, h482, h542, h548, h550, h552, hlam]
                            · linarith only [h1, h549, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi5]
                          · linarith only [h1, h482, h485, h528, h548, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi6]
                · linarith only [h1, h481, h527, hlam]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h562 | h562
          · linarith only [h0, h1, h562, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h564 | h564
            · rcases m.htr 0 2 5 (by decide) (by decide) with h565 | h565
              · linarith only [h0, h482, h565, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h567 | h567
                · rcases m.htr 0 4 5 (by decide) (by decide) with h568 | h568
                  · linarith only [h0, h482, h564, h568, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h570 | h570
                    · linarith only [h562, h570, hc12, hlam, hphi, ht01, u0ehi6]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h572 | h572
                      · linarith only [h0, h572, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi2]
                      · linarith only [h564, h565, h572, hc12, hc25, hlam, hphi]
                · linarith only [h1, h481, h567, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h576 | h576
              · linarith only [h481, h482, h564, h576, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h578 | h578
                · rcases m.htr 0 4 5 (by decide) (by decide) with h579 | h579
                  · linarith only [h481, h482, h579, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h581 | h581
                    · linarith only [h0, h562, h581, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h583 | h583
                      · linarith only [h0, h1, h564, h581, h583, hc23, hlam, hphi, ht01, ht12, u0ehi6]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h585 | h585
                        · linarith only [h1, h481, h576, h581, h583, h585, hc23, hlam, hphi, ht01, ht12, u0ehi6]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h587 | h587
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h588 | h588
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h589 | h589
                              · linarith only [h481, h482, h579, h581, h588, h589, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi0]
                              · linarith only [h481, h482, h589, hc45, hlam, hphi, u4ehi1]
                            · linarith only [h1, h481, h587, h588, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi3]
                          · linarith only [h1, h481, h587, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi1]
                · linarith only [h1, h481, h578, hlam]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h595 | h595
        · rcases m.htr 0 2 3 (by decide) (by decide) with h596 | h596
          · linarith only [h0, h1, h596, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h598 | h598
            · linarith only [h0, h481, h598, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h600 | h600
              · rcases m.htr 0 3 4 (by decide) (by decide) with h601 | h601
                · rcases m.htr 0 4 5 (by decide) (by decide) with h602 | h602
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h603 | h603
                    · linarith only [h596, h603, hc12, hlam, hphi, ht01, u0ehi6]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h605 | h605
                      · linarith only [h0, h1, h598, h600, h603, h605, hc23, hlam, hphi, ht01, ht12, u0ehi9]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h607 | h607
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h608 | h608
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h609 | h609
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h610 | h610
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h611 | h611
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h612 | h612
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h613 | h613
                                    · linarith only [h0, h481, h603, h607, h608, h613, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                                    · linarith only [h0, h481, h605, h613, hc12, hc45, hlam, hphi, ht23, ht34]
                                  · linarith only [h0, h1, h603, h607, h610, h612, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
                                · linarith only [h0, h481, h601, h603, h607, h608, h610, h611, hlam, hphi, ht0b, ht45, ht5b, u0elo2, u4ehi4]
                              · linarith only [h0, h481, h610, hc12, hc45, hlam, hphi, ht23, ht34]
                            · linarith only [h0, h481, h600, h608, h609, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi9]
                          · linarith only [h0, h1, h600, h601, h608, hlam, hphi, u0ehi9, u0elo2]
                        · linarith only [h0, h481, h600, h605, h607, hc12, hc24, hlam, hphi]
                  · linarith only [h481, h595, h602, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h623 | h623
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h624 | h624
                    · linarith only [h596, h624, hc12, hlam, hphi, ht01, u0ehi6]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h626 | h626
                      · linarith only [h0, h1, h601, h626, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi2]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h628 | h628
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h629 | h629
                          · linarith only [h0, h1, h601, h624, h629, hc12, hc23, hlam, hphi]
                          · linarith only [h0, h1, h600, h629, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi9]
                        · linarith only [h0, h481, h600, h626, h628, hc12, hc24, hlam, hphi]
                  · linarith only [h0, h1, h600, h601, h623, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h634 | h634
                · rcases m.htr 0 4 5 (by decide) (by decide) with h635 | h635
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h636 | h636
                    · linarith only [h596, h636, hc12, hlam, hphi, ht01, u0ehi6]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h638 | h638
                      · linarith only [h0, h1, h636, h638, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h640 | h640
                        · linarith only [h0, h1, h600, h636, h640, hc23, hlam, hphi, ht01, ht12, u0ehi6]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h642 | h642
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h643 | h643
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h644 | h644
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h645 | h645
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h646 | h646
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h647 | h647
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h648 | h648
                                      · linarith only [h634, h648, hlam, hphi, ht0b, ht45, ht5b, u0elo2, u4ehi4]
                                      · linarith only [h635, h648, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi3]
                                    · linarith only [h481, h595, h638, h644, h647, hlam]
                                  · linarith only [h481, h595, h636, h642, h643, h646, hlam]
                                · linarith only [h481, h595, h636, h640, h642, h645, hc12, hc34, hlam, hphi, ht23]
                              · linarith only [h481, h595, h600, h644, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi6]
                            · linarith only [h481, h595, h600, h642, h643, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi6]
                          · linarith only [h1, h595, h600, h634, h642, hlam, hphi, u0ehi6, u0elo2]
                  · linarith only [h481, h595, h635, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h658 | h658
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h659 | h659
                    · linarith only [h596, h659, hc12, hlam, hphi, ht01, u0ehi6]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h661 | h661
                      · linarith only [h0, h661, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi2]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h663 | h663
                        · linarith only [h0, h1, h600, h634, h663, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi6]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h665 | h665
                          · linarith only [h1, h595, h634, h659, h663, h665, hc12, hc23, hlam, hphi]
                          · linarith only [h1, h595, h600, h665, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi6]
                  · linarith only [h1, h595, h634, h658, hlam]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h669 | h669
          · linarith only [h0, h1, h669, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h671 | h671
            · linarith only [h0, h481, h671, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h673 | h673
              · linarith only [h0, h595, h673, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h675 | h675
                · rcases m.htr 0 4 5 (by decide) (by decide) with h676 | h676
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h677 | h677
                    · linarith only [h669, h677, hc12, hlam, hphi, ht01, u0ehi6]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h679 | h679
                      · linarith only [h0, h671, h679, hlam, hphi, u0ehi6, u0elo0]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h681 | h681
                        · linarith only [h0, h595, h673, h675, h676, h681, hlam, hphi, u0ehi6, u0elo2]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h683 | h683
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h684 | h684
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h685 | h685
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h686 | h686
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h687 | h687
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h688 | h688
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h689 | h689
                                      · linarith only [h675, h689, hlam, hphi, ht0b, ht45, ht5b, u0elo2, u4ehi4]
                                      · linarith only [h675, h676, h689, hlam, hphi, ht0b, ht45, ht5b, u0elo2, u4ehi3]
                                    · linarith only [h595, h675, h676, h679, h685, h688, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                                  · linarith only [h677, h684, h687, hlam]
                                · linarith only [h0, h595, h677, h683, h685, h686, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi6]
                              · linarith only [h675, h676, h685, hlam, hphi, ht0b, ht45, ht5b, u0elo2, u4ehi1]
                            · linarith only [h0, h481, h683, h684, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi6]
                          · linarith only [h0, h1, h675, h683, hlam, hphi, u0ehi6, u0elo2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h698 | h698
                    · linarith only [h0, h669, h698, hlam, hphi, u0ehi6, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h700 | h700
                      · linarith only [h0, h481, h676, h700, hc45, hlam, hphi, u4ehi2]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h702 | h702
                        · linarith only [h0, h481, h673, h676, h702, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi6]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h704 | h704
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h705 | h705
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h706 | h706
                              · linarith only [h0, h481, h676, h698, h704, h706, hc12, hc23, hlam, hphi]
                              · linarith only [h0, h481, h706, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi6]
                            · linarith only [h0, h1, h705, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi6]
                          · linarith only [h0, h1, h675, h704, hlam, hphi, u0ehi6, u0elo2]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h711 | h711
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h712 | h712
                    · linarith only [h0, h669, h712, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h714 | h714
                      · linarith only [h0, h1, h675, h714, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi2]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h716 | h716
                        · linarith only [h0, h1, h673, h675, h716, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi6]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h718 | h718
                          · linarith only [h0, h1, h675, h712, h718, hc12, hc23, hlam, hphi]
                          · linarith only [h0, h1, h718, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi6]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h721 | h721
                    · linarith only [h0, h481, h711, h721, hc23, hc45, hlam, hphi, ht34]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h723 | h723
                      · linarith only [h0, h1, h675, h711, h723, hc45, hlam, hphi, u4ehi2]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h725 | h725
                        · linarith only [h0, h1, h673, h675, h711, h725, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi6]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h727 | h727
                          · linarith only [h0, h1, h675, h721, h727, hc12, hc23, hlam, hphi]
                          · linarith only [h0, h1, h727, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi6]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h730 | h730
    · rcases m.htr 0 1 4 (by decide) (by decide) with h731 | h731
      · rcases m.htr 0 1 5 (by decide) (by decide) with h732 | h732
        · rcases m.htr 0 2 3 (by decide) (by decide) with h733 | h733
          · rcases m.htr 0 2 4 (by decide) (by decide) with h734 | h734
            · rcases m.htr 0 2 5 (by decide) (by decide) with h735 | h735
              · rcases m.htr 0 3 4 (by decide) (by decide) with h736 | h736
                · rcases m.htr 0 4 5 (by decide) (by decide) with h737 | h737
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h738 | h738
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h739 | h739
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h740 | h740
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h741 | h741
                          · linarith only [h730, h741, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi3]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h743 | h743
                            · linarith only [h0, h730, h736, h741, h743, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h745 | h745
                              · linarith only [h0, h731, h745, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi4]
                              · linarith only [h737, h745, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi1]
                        · linarith only [h0, h730, h736, h740, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                      · linarith only [h0, h730, h736, h739, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                    · linarith only [h0, h730, h736, h737, h738, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h751 | h751
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h752 | h752
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h753 | h753
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h754 | h754
                          · linarith only [h0, h730, h754, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi3]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h756 | h756
                            · linarith only [h0, h730, h736, h754, h756, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h758 | h758
                              · linarith only [h0, h731, h758, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h760 | h760
                                · linarith only [h751, h754, h760, hlam]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h762 | h762
                                  · linarith only [h0, h730, h736, h751, h754, h756, h762, hc12, hc15, hlam, hphi, ht01, ht0b, ht5b]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h764 | h764
                                    · linarith only [h0, h730, h736, h737, h752, h754, h764, hc12, hlam, hphi, ht01, u0ehi8]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h766 | h766
                                      · linarith only [h0, h730, h736, h737, h766, hc12, hlam, hphi, ht01, u0ehi8]
                                      · rcases h1bigk with h768c | h768c | h768c | h768c | h768c | h768c | h768c | h768c | h768c | h768c | h768c | h768c | h768c | h768c | h768c | h768c | h768c | h768c | h768c | h768c | h768c | h768c | h768c | h768c | h768c
                                        · have p768_0 := h768c.1
                                          have p768_1 := h768c.2.1
                                          have p768_2 := h768c.2.2.1
                                          have p768_3 := h768c.2.2.2
                                          linarith only [hlam, p768_0]
                                        · have p768_0 := h768c.1
                                          have p768_1 := h768c.2.1
                                          have p768_2 := h768c.2.2.1
                                          have p768_3 := h768c.2.2.2
                                          linarith only [h0, hlam, p768_0]
                                        · have p768_0 := h768c.1
                                          have p768_1 := h768c.2.1
                                          have p768_2 := h768c.2.2.1
                                          have p768_3 := h768c.2.2.2
                                          rcases p768_3 (m.d 0 1) (by simp) with h771 | h771
                                          · rcases p768_3 (m.d 1 2) (by simp) with h772 | h772
                                            · rcases p768_3 (m.d 1 3) (by simp) with h773 | h773
                                              · linarith only [h773, hlam, p768_0]
                                              · rcases p768_3 (m.d 1 4) (by simp) with h775 | h775
                                                · linarith only [h731, h775, hlam]
                                                · linarith only [h754, h775, hlam]
                                            · linarith only [h751, h772, hlam]
                                          · linarith only [h771, hlam, p768_0]
                                        · have p768_0 := h768c.1
                                          have p768_1 := h768c.2.1
                                          have p768_2 := h768c.2.2.1
                                          have p768_3 := h768c.2.2.2
                                          linarith only [h0, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p768_1, u4ehi1]
                                        · have p768_0 := h768c.1
                                          have p768_1 := h768c.2.1
                                          have p768_2 := h768c.2.2.1
                                          have p768_3 := h768c.2.2.2
                                          linarith only [h0, h758, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p768_1, u4ehi1]
                                        · have p768_0 := h768c.1
                                          have p768_1 := h768c.2.1
                                          have p768_2 := h768c.2.2.1
                                          have p768_3 := h768c.2.2.2
                                          linarith only [h730, h736, h754, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p768_1]
                                        · have p768_0 := h768c.1
                                          have p768_1 := h768c.2.1
                                          have p768_2 := h768c.2.2.1
                                          have p768_3 := h768c.2.2.2
                                          linarith only [hlam, p768_0]
                                        · have p768_0 := h768c.1
                                          have p768_1 := h768c.2.1
                                          have p768_2 := h768c.2.2.1
                                          have p768_3 := h768c.2.2.2
                                          linarith only [h0, h730, h736, h754, hlam, p768_2]
                                        · have p768_0 := h768c.1
                                          have p768_1 := h768c.2.1
                                          have p768_2 := h768c.2.2.1
                                          have p768_3 := h768c.2.2.2
                                          rcases p768_3 (m.d 0 1) (by simp) with h785 | h785
                                          · linarith only [h0, h785, hlam]
                                          · linarith only [h731, h785, hlam]
                                        · have p768_0 := h768c.1
                                          have p768_1 := h768c.2.1
                                          have p768_2 := h768c.2.2.1
                                          have p768_3 := h768c.2.2.2
                                          rcases p768_3 (m.d 0 1) (by simp) with h788 | h788
                                          · linarith only [h0, h788, hlam]
                                          · linarith only [h732, h788, hlam]
                                        · have p768_0 := h768c.1
                                          have p768_1 := h768c.2.1
                                          have p768_2 := h768c.2.2.1
                                          have p768_3 := h768c.2.2.2
                                          linarith only [h730, hlam, p768_0]
                                        · have p768_0 := h768c.1
                                          have p768_1 := h768c.2.1
                                          have p768_2 := h768c.2.2.1
                                          have p768_3 := h768c.2.2.2
                                          linarith only [h751, hlam, p768_1]
                                        · have p768_0 := h768c.1
                                          have p768_1 := h768c.2.1
                                          have p768_2 := h768c.2.2.1
                                          have p768_3 := h768c.2.2.2
                                          linarith only [hlam, p768_0]
                                        · have p768_0 := h768c.1
                                          have p768_1 := h768c.2.1
                                          have p768_2 := h768c.2.2.1
                                          have p768_3 := h768c.2.2.2
                                          linarith only [h754, hlam, p768_1]
                                        · have p768_0 := h768c.1
                                          have p768_1 := h768c.2.1
                                          have p768_2 := h768c.2.2.1
                                          have p768_3 := h768c.2.2.2
                                          linarith only [h756, hlam, p768_1]
                                        · have p768_0 := h768c.1
                                          have p768_1 := h768c.2.1
                                          have p768_2 := h768c.2.2.1
                                          have p768_3 := h768c.2.2.2
                                          linarith only [h731, hlam, p768_0]
                                        · have p768_0 := h768c.1
                                          have p768_1 := h768c.2.1
                                          have p768_2 := h768c.2.2.1
                                          have p768_3 := h768c.2.2.2
                                          linarith only [h752, hlam, p768_1]
                                        · have p768_0 := h768c.1
                                          have p768_1 := h768c.2.1
                                          have p768_2 := h768c.2.2.1
                                          have p768_3 := h768c.2.2.2
                                          linarith only [h731, h751, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p768_1, u0elo0]
                                        · have p768_0 := h768c.1
                                          have p768_1 := h768c.2.1
                                          have p768_2 := h768c.2.2.1
                                          have p768_3 := h768c.2.2.2
                                          linarith only [hlam, p768_0]
                                        · have p768_0 := h768c.1
                                          have p768_1 := h768c.2.1
                                          have p768_2 := h768c.2.2.1
                                          have p768_3 := h768c.2.2.2
                                          linarith only [h758, hlam, p768_1]
                                        · have p768_0 := h768c.1
                                          have p768_1 := h768c.2.1
                                          have p768_2 := h768c.2.2.1
                                          have p768_3 := h768c.2.2.2
                                          linarith only [h732, hlam, p768_0]
                                        · have p768_0 := h768c.1
                                          have p768_1 := h768c.2.1
                                          have p768_2 := h768c.2.2.1
                                          have p768_3 := h768c.2.2.2
                                          linarith only [h753, hlam, p768_1]
                                        · have p768_0 := h768c.1
                                          have p768_1 := h768c.2.1
                                          have p768_2 := h768c.2.2.1
                                          have p768_3 := h768c.2.2.2
                                          linarith only [h0, h732, h751, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p768_1, u0elo1]
                                        · have p768_0 := h768c.1
                                          have p768_1 := h768c.2.1
                                          have p768_2 := h768c.2.2.1
                                          have p768_3 := h768c.2.2.2
                                          linarith only [h0, h732, hlam, hphi, ht0b, ht45, ht5b, p768_1, u0elo1, u4ehi1]
                                        · have p768_0 := h768c.1
                                          have p768_1 := h768c.2.1
                                          have p768_2 := h768c.2.2.1
                                          have p768_3 := h768c.2.2.2
                                          linarith only [hlam, p768_0]
                        · linarith only [h0, h753, hc25, hlam, hphi, ht01, ht12, u0ehi5]
                      · linarith only [h0, h730, h736, h752, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                    · linarith only [h0, h730, h736, h751, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h809 | h809
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h810 | h810
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h811 | h811
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h812 | h812
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h813 | h813
                          · linarith only [h736, h813, hc13, hlam, hphi, ht01, u0ehi7]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h815 | h815
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h816 | h816
                              · linarith only [h731, h816, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi4]
                              · linarith only [h0, h731, h809, h816, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi1]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h819 | h819
                              · linarith only [h0, h731, h819, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                              · linarith only [h0, h731, h809, h819, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi1]
                        · linarith only [h0, h812, hc25, hlam, hphi, ht01, ht12, u0ehi5]
                      · linarith only [h0, h731, h809, h811, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                    · linarith only [h0, h731, h809, h810, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h825 | h825
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h826 | h826
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h827 | h827
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h828 | h828
                          · linarith only [h736, h828, hc13, hlam, hphi, ht01, u0ehi7]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h830 | h830
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h831 | h831
                              · linarith only [h809, h831, hc14, hlam, hphi, ht01, u0ehi8]
                              · linarith only [h828, h830, h831, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h834 | h834
                              · linarith only [h736, h809, h834, hc14, hlam, hphi, ht01, u0ehi7]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h836 | h836
                                · linarith only [h732, h736, h825, h828, h834, h836, hlam, hphi, u0ehi7, u0elo0]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h838 | h838
                                  · linarith only [h733, h830, h838, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h840 | h840
                                    · linarith only [h0, h732, h736, h809, h826, h834, h840, hc12, hlam, hphi, ht01, u0ehi7]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h842 | h842
                                      · linarith only [h736, h809, h842, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi7]
                                      · linarith only [h736, h842, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi7]
                        · linarith only [h0, h735, h827, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                      · linarith only [h0, h732, h736, h809, h826, hc24, hlam, hphi, ht01, ht12, u0ehi7]
                    · linarith only [h0, h732, h736, h809, h825, hc23, hlam, hphi, ht01, ht12, u0ehi7]
              · linarith only [h0, h732, h735, hlam]
            · linarith only [h0, h731, h734, hlam]
          · linarith only [h0, h730, h733, hlam]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h851 | h851
          · rcases m.htr 0 2 4 (by decide) (by decide) with h852 | h852
            · rcases m.htr 0 2 5 (by decide) (by decide) with h853 | h853
              · rcases m.htr 0 3 4 (by decide) (by decide) with h854 | h854
                · rcases m.htr 0 4 5 (by decide) (by decide) with h855 | h855
                  · linarith only [h730, h732, h854, h855, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h857 | h857
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h858 | h858
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h859 | h859
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h860 | h860
                          · linarith only [h730, h860, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi3]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h862 | h862
                            · linarith only [h730, h732, h853, h854, h860, h862, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
                            · linarith only [h730, h732, h854, h860, h862, hc13, hc35, hlam, hphi]
                        · linarith only [h0, h853, h859, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                      · linarith only [h0, h730, h854, h858, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                    · linarith only [h0, h730, h854, h857, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h868 | h868
                  · linarith only [h731, h732, h868, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h870 | h870
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h871 | h871
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h872 | h872
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h873 | h873
                          · linarith only [h854, h873, hc13, hlam, hphi, ht01, u0ehi7]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h875 | h875
                            · linarith only [h731, h732, h873, h875, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h877 | h877
                              · linarith only [h731, h732, h868, h875, h877, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi0]
                              · linarith only [h731, h732, h877, hc45, hlam, hphi, u4ehi1]
                        · linarith only [h0, h731, h853, h871, h872, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi2]
                      · linarith only [h0, h731, h871, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
                    · linarith only [h0, h731, h870, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h883 | h883
                · rcases m.htr 0 4 5 (by decide) (by decide) with h884 | h884
                  · linarith only [h0, h730, h853, h883, h884, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h886 | h886
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h887 | h887
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h888 | h888
                        · linarith only [h0, h853, h888, hc12, hlam, hphi, ht01, u0ehi5]
                        · linarith only [h0, h731, h887, h888, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
                      · linarith only [h0, h731, h887, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
                    · linarith only [h0, h730, h883, h886, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi3]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h893 | h893
                  · linarith only [h0, h731, h853, h893, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h895 | h895
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h896 | h896
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h897 | h897
                        · linarith only [h0, h731, h853, h896, h897, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                        · linarith only [h0, h731, h896, h897, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
                      · linarith only [h0, h731, h896, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
                    · linarith only [h0, h731, h895, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
            · linarith only [h0, h731, h852, hlam]
          · linarith only [h0, h730, h851, hlam]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h904 | h904
        · rcases m.htr 0 2 3 (by decide) (by decide) with h905 | h905
          · rcases m.htr 0 2 4 (by decide) (by decide) with h906 | h906
            · rcases m.htr 0 2 5 (by decide) (by decide) with h907 | h907
              · rcases m.htr 0 3 4 (by decide) (by decide) with h908 | h908
                · linarith only [h730, h731, h908, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h910 | h910
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h911 | h911
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h912 | h912
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h913 | h913
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h914 | h914
                          · linarith only [h730, h908, h914, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h916 | h916
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h917 | h917
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h918 | h918
                                · linarith only [h730, h731, h911, h914, h918, hlam]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h920 | h920
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h921 | h921
                                    · linarith only [h906, h921, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi4]
                                    · linarith only [h906, h910, h921, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi2]
                                  · linarith only [h730, h731, h914, h916, h920, hc23, hc34, hlam, hphi]
                              · linarith only [h730, h731, h917, hc13, hc45, hlam, hphi, ht34]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h926 | h926
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h927 | h927
                                · linarith only [h905, h927, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi3]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h929 | h929
                                  · linarith only [h911, h916, h929, hlam]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h931 | h931
                                    · linarith only [h906, h931, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi4]
                                    · linarith only [h904, h926, h931, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi2]
                              · linarith only [h731, h906, h910, h926, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                        · linarith only [h731, h904, h912, h913, hc25, hlam, hphi, ht01, ht12, u0ehi9]
                      · linarith only [h0, h904, h912, hc24, hlam, hphi, ht01, ht12, u0ehi9]
                    · linarith only [h0, h904, h911, hc23, hlam, hphi, ht01, ht12, u0ehi9]
                  · linarith only [h731, h904, h910, hlam]
              · linarith only [h0, h904, h907, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h940 | h940
              · rcases m.htr 0 3 4 (by decide) (by decide) with h941 | h941
                · linarith only [h0, h730, h906, h941, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h943 | h943
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h944 | h944
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h945 | h945
                      · linarith only [h0, h906, h945, hc12, hlam, hphi, ht01, u0ehi5]
                      · linarith only [h0, h730, h945, hc24, hlam, hphi, ht01, ht12, u0ehi7]
                    · linarith only [h0, h730, h944, hc23, hlam, hphi, ht01, ht12, u0ehi7]
                  · linarith only [h0, h904, h906, h943, hlam]
              · linarith only [h0, h904, h940, hlam]
          · linarith only [h0, h730, h905, hlam]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h952 | h952
          · rcases m.htr 0 2 4 (by decide) (by decide) with h953 | h953
            · rcases m.htr 0 2 5 (by decide) (by decide) with h954 | h954
              · rcases m.htr 0 3 4 (by decide) (by decide) with h955 | h955
                · linarith only [h730, h731, h955, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h957 | h957
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h958 | h958
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h959 | h959
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h960 | h960
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h961 | h961
                          · linarith only [h730, h955, h961, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h963 | h963
                            · linarith only [h730, h904, h963, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h965 | h965
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h966 | h966
                                · linarith only [h730, h904, h958, h961, h965, h966, hlam]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h968 | h968
                                  · linarith only [h730, h904, h958, h963, h968, hlam]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h970 | h970
                                    · linarith only [h953, h970, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi4]
                                    · linarith only [h953, h957, h970, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi2]
                              · linarith only [h953, h957, h965, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi1]
                        · linarith only [h730, h731, h954, h959, h960, hlam, hphi, u0ehi7, u0elo1]
                      · linarith only [h0, h730, h959, hc24, hlam, hphi, ht01, ht12, u0ehi7]
                    · linarith only [h0, h730, h958, hc23, hlam, hphi, ht01, ht12, u0ehi7]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h977 | h977
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h978 | h978
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h979 | h979
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h980 | h980
                          · linarith only [h955, h980, hc13, hlam, hphi, ht01, u0ehi7]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h982 | h982
                            · linarith only [h730, h904, h982, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h984 | h984
                              · linarith only [h730, h731, h957, h978, h984, hc12, hlam, hphi, ht01, u0ehi7]
                              · linarith only [h730, h731, h984, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi7]
                        · linarith only [h0, h730, h954, h979, hlam, hphi, u0ehi7, u0elo1]
                      · linarith only [h0, h730, h953, h978, hlam, hphi, u0ehi7, u0elo1]
                    · linarith only [h0, h730, h977, hc23, hlam, hphi, ht01, ht12, u0ehi7]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h990 | h990
                · linarith only [h730, h731, h990, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h992 | h992
                  · linarith only [h953, h954, h992, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h994 | h994
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h995 | h995
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h996 | h996
                        · linarith only [h730, h731, h953, h954, h992, h996, hc12, hc45, hlam, hphi, ht01, u0ehi7, u4ehi2]
                        · linarith only [h0, h730, h996, hc25, hlam, hphi, ht01, ht12, u0ehi7]
                      · linarith only [h0, h730, h953, h995, hlam, hphi, u0ehi7, u0elo1]
                    · linarith only [h0, h730, h994, hc23, hlam, hphi, ht01, ht12, u0ehi7]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h1001 | h1001
              · rcases m.htr 0 3 4 (by decide) (by decide) with h1002 | h1002
                · linarith only [h0, h1002, h730, h953, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1004 | h1004
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1005 | h1005
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1006 | h1006
                      · linarith only [h1001, h1006, h904, h953, hc12, hlam, hphi, ht01, u0ehi5]
                      · linarith only [h0, h1006, h730, hc24, hlam, hphi, ht01, ht12, u0ehi7]
                    · linarith only [h0, h1005, h730, hc23, hlam, hphi, ht01, ht12, u0ehi7]
                  · linarith only [h1001, h1004, h953, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h1011 | h1011
                · linarith only [h0, h1011, h730, h953, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1013 | h1013
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1014 | h1014
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1015 | h1015
                      · linarith only [h0, h1015, h953, hc12, hlam, hphi, ht01, u0ehi5]
                      · linarith only [h0, h1015, h730, hc24, hlam, hphi, ht01, ht12, u0ehi7]
                    · linarith only [h0, h1014, h730, hc23, hlam, hphi, ht01, ht12, u0ehi7]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1019 | h1019
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1020 | h1020
                      · linarith only [h0, h1020, h730, h953, hc12, hlam, hphi, ht01, u0ehi7]
                      · linarith only [h0, h1020, h730, hc24, hlam, hphi, ht01, ht12, u0ehi7]
                    · linarith only [h0, h1019, h730, hc23, hlam, hphi, ht01, ht12, u0ehi7]
          · linarith only [h0, h730, h952, hlam]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h1025 | h1025
      · rcases m.htr 0 1 5 (by decide) (by decide) with h1026 | h1026
        · rcases m.htr 0 2 3 (by decide) (by decide) with h1027 | h1027
          · rcases m.htr 0 2 4 (by decide) (by decide) with h1028 | h1028
            · rcases m.htr 0 2 5 (by decide) (by decide) with h1029 | h1029
              · rcases m.htr 0 3 4 (by decide) (by decide) with h1030 | h1030
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1031 | h1031
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1032 | h1032
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1033 | h1033
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1034 | h1034
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1035 | h1035
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1036 | h1036
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1037 | h1037
                              · linarith only [h1025, h1037, hlam, hphi, ht0b, ht45, ht5b, u0elo0, u4ehi4]
                              · linarith only [h1025, h1027, h1031, h1037, h730, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi1]
                            · linarith only [h1036, h730, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi5]
                          · linarith only [h1025, h1031, h1035, h730, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi4]
                        · linarith only [h1025, h1031, h1032, h1034, h730, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                      · linarith only [h1025, h1031, h1032, h1033, h730, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi4]
                    · linarith only [h0, h1025, h1027, h1031, h1032, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi4]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1045 | h1045
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1046 | h1046
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1047 | h1047
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1048 | h1048
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1049 | h1049
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1050 | h1050
                              · linarith only [h1025, h1031, h1050, hlam, hphi, u0ehi8, u0elo0]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1052 | h1052
                                · linarith only [h1027, h1052, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi3]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h1054 | h1054
                                  · linarith only [h1026, h1045, h1048, h1050, h1052, h1054, h730, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1056 | h1056
                                    · linarith only [h1026, h1031, h1045, h1048, h1050, h1052, h1056, h730, hc12, hlam, hphi, ht01, u0ehi8]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h1058 | h1058
                                      · linarith only [h1026, h1031, h1045, h1048, h1050, h1058, h730, hc12, hlam, hphi, ht01, u0ehi8]
                                      · rcases h1bigk with h1060c | h1060c | h1060c | h1060c | h1060c | h1060c | h1060c | h1060c | h1060c | h1060c | h1060c | h1060c | h1060c | h1060c | h1060c | h1060c | h1060c | h1060c | h1060c | h1060c | h1060c | h1060c | h1060c | h1060c | h1060c
                                        · have p1060_0 := h1060c.1
                                          have p1060_1 := h1060c.2.1
                                          have p1060_2 := h1060c.2.2.1
                                          have p1060_3 := h1060c.2.2.2
                                          linarith only [hlam, p1060_0]
                                        · have p1060_0 := h1060c.1
                                          have p1060_1 := h1060c.2.1
                                          have p1060_2 := h1060c.2.2.1
                                          have p1060_3 := h1060c.2.2.2
                                          linarith only [h0, hlam, p1060_0]
                                        · have p1060_0 := h1060c.1
                                          have p1060_1 := h1060c.2.1
                                          have p1060_2 := h1060c.2.2.1
                                          have p1060_3 := h1060c.2.2.2
                                          linarith only [h730, hlam, p1060_0]
                                        · have p1060_0 := h1060c.1
                                          have p1060_1 := h1060c.2.1
                                          have p1060_2 := h1060c.2.2.1
                                          have p1060_3 := h1060c.2.2.2
                                          linarith only [h1045, h730, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, p1060_1, u4ehi1]
                                        · have p1060_0 := h1060c.1
                                          have p1060_1 := h1060c.2.1
                                          have p1060_2 := h1060c.2.2.1
                                          have p1060_3 := h1060c.2.2.2
                                          linarith only [h1045, h1048, h1050, h1052, h730, hc12, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1060_1]
                                        · have p1060_0 := h1060c.1
                                          have p1060_1 := h1060c.2.1
                                          have p1060_2 := h1060c.2.2.1
                                          have p1060_3 := h1060c.2.2.2
                                          linarith only [hc12, hlam, hphi, ht01, p1060_1, u0ehi5]
                                        · have p1060_0 := h1060c.1
                                          have p1060_1 := h1060c.2.1
                                          have p1060_2 := h1060c.2.2.1
                                          have p1060_3 := h1060c.2.2.2
                                          linarith only [hlam, p1060_0]
                                        · have p1060_0 := h1060c.1
                                          have p1060_1 := h1060c.2.1
                                          have p1060_2 := h1060c.2.2.1
                                          have p1060_3 := h1060c.2.2.2
                                          linarith only [h730, hc12, hlam, hphi, ht01, p1060_1, u0ehi5]
                                        · have p1060_0 := h1060c.1
                                          have p1060_1 := h1060c.2.1
                                          have p1060_2 := h1060c.2.2.1
                                          have p1060_3 := h1060c.2.2.2
                                          rcases p1060_3 (m.d 0 1) (by simp) with h1069 | h1069
                                          · linarith only [h0, h1069, hlam]
                                          · linarith only [h1025, h1069, hlam]
                                        · have p1060_0 := h1060c.1
                                          have p1060_1 := h1060c.2.1
                                          have p1060_2 := h1060c.2.2.1
                                          have p1060_3 := h1060c.2.2.2
                                          rcases p1060_3 (m.d 0 1) (by simp) with h1072 | h1072
                                          · linarith only [h0, h1072, hlam]
                                          · linarith only [h1026, h1072, hlam]
                                        · have p1060_0 := h1060c.1
                                          have p1060_1 := h1060c.2.1
                                          have p1060_2 := h1060c.2.2.1
                                          have p1060_3 := h1060c.2.2.2
                                          linarith only [h1026, h1048, h1050, h1052, hc13, hc23, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p1060_1]
                                        · have p1060_0 := h1060c.1
                                          have p1060_1 := h1060c.2.1
                                          have p1060_2 := h1060c.2.2.1
                                          have p1060_3 := h1060c.2.2.2
                                          linarith only [h1045, hlam, p1060_1]
                                        · have p1060_0 := h1060c.1
                                          have p1060_1 := h1060c.2.1
                                          have p1060_2 := h1060c.2.2.1
                                          have p1060_3 := h1060c.2.2.2
                                          linarith only [hlam, p1060_0]
                                        · have p1060_0 := h1060c.1
                                          have p1060_1 := h1060c.2.1
                                          have p1060_2 := h1060c.2.2.1
                                          have p1060_3 := h1060c.2.2.2
                                          rcases p1060_3 (m.d 0 1) (by simp) with h1078 | h1078
                                          · linarith only [h1078, h730, hlam]
                                          · linarith only [h1025, h1078, hlam]
                                        · have p1060_0 := h1060c.1
                                          have p1060_1 := h1060c.2.1
                                          have p1060_2 := h1060c.2.2.1
                                          have p1060_3 := h1060c.2.2.2
                                          rcases p1060_3 (m.d 0 1) (by simp) with h1081 | h1081
                                          · linarith only [h1081, h730, hlam]
                                          · linarith only [h1026, h1081, hlam]
                                        · have p1060_0 := h1060c.1
                                          have p1060_1 := h1060c.2.1
                                          have p1060_2 := h1060c.2.2.1
                                          have p1060_3 := h1060c.2.2.2
                                          linarith only [h1025, hlam, p1060_0]
                                        · have p1060_0 := h1060c.1
                                          have p1060_1 := h1060c.2.1
                                          have p1060_2 := h1060c.2.2.1
                                          have p1060_3 := h1060c.2.2.2
                                          linarith only [h1046, hlam, p1060_1]
                                        · have p1060_0 := h1060c.1
                                          have p1060_1 := h1060c.2.1
                                          have p1060_2 := h1060c.2.2.1
                                          have p1060_3 := h1060c.2.2.2
                                          linarith only [h1048, hlam, p1060_0]
                                        · have p1060_0 := h1060c.1
                                          have p1060_1 := h1060c.2.1
                                          have p1060_2 := h1060c.2.2.1
                                          have p1060_3 := h1060c.2.2.2
                                          linarith only [hlam, p1060_0]
                                        · have p1060_0 := h1060c.1
                                          have p1060_1 := h1060c.2.1
                                          have p1060_2 := h1060c.2.2.1
                                          have p1060_3 := h1060c.2.2.2
                                          linarith only [h1050, hlam, p1060_1]
                                        · have p1060_0 := h1060c.1
                                          have p1060_1 := h1060c.2.1
                                          have p1060_2 := h1060c.2.2.1
                                          have p1060_3 := h1060c.2.2.2
                                          linarith only [h1026, hlam, p1060_0]
                                        · have p1060_0 := h1060c.1
                                          have p1060_1 := h1060c.2.1
                                          have p1060_2 := h1060c.2.2.1
                                          have p1060_3 := h1060c.2.2.2
                                          linarith only [h1047, hlam, p1060_1]
                                        · have p1060_0 := h1060c.1
                                          have p1060_1 := h1060c.2.1
                                          have p1060_2 := h1060c.2.2.1
                                          have p1060_3 := h1060c.2.2.2
                                          linarith only [h1049, hlam, p1060_0]
                                        · have p1060_0 := h1060c.1
                                          have p1060_1 := h1060c.2.1
                                          have p1060_2 := h1060c.2.2.1
                                          have p1060_3 := h1060c.2.2.2
                                          linarith only [h1026, h1048, h1052, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, p1060_1, u0elo0]
                                        · have p1060_0 := h1060c.1
                                          have p1060_1 := h1060c.2.1
                                          have p1060_2 := h1060c.2.2.1
                                          have p1060_3 := h1060c.2.2.2
                                          linarith only [hlam, p1060_0]
                            · linarith only [h1049, h730, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi5]
                          · linarith only [h1025, h1046, h1048, h730, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi2]
                        · linarith only [h0, h1025, h1046, h1047, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
                      · linarith only [h1025, h1045, h1046, h730, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
                    · linarith only [h0, h1025, h1045, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
                · linarith only [h1025, h1030, h730, hlam]
              · linarith only [h0, h1026, h1029, hlam]
            · linarith only [h1025, h1027, h1028, h730, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h1102 | h1102
            · rcases m.htr 0 2 5 (by decide) (by decide) with h1103 | h1103
              · rcases m.htr 0 3 4 (by decide) (by decide) with h1104 | h1104
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1105 | h1105
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1106 | h1106
                    · linarith only [h1027, h1102, h1106, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                    · linarith only [h0, h1106, hc23, hlam, hphi, ht01, ht12, u0ehi5]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1109 | h1109
                    · linarith only [h0, h1025, h1027, h1109, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi1]
                    · linarith only [h0, h1025, h1109, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
                · linarith only [h0, h1025, h1027, h1104, hlam]
              · linarith only [h0, h1026, h1103, hlam]
            · linarith only [h0, h1025, h1102, hlam]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h1115 | h1115
          · rcases m.htr 0 2 4 (by decide) (by decide) with h1116 | h1116
            · rcases m.htr 0 2 5 (by decide) (by decide) with h1117 | h1117
              · rcases m.htr 0 3 4 (by decide) (by decide) with h1118 | h1118
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1119 | h1119
                  · linarith only [h1025, h1026, h1119, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1121 | h1121
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1122 | h1122
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1123 | h1123
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1124 | h1124
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1125 | h1125
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1126 | h1126
                              · linarith only [h1119, h1126, hc14, hlam, hphi, ht01, u0ehi8]
                              · linarith only [h1025, h1026, h1122, h1126, hc45, hlam, hphi, u4ehi2]
                            · linarith only [h1025, h1122, h1125, h730, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi2]
                          · linarith only [h1025, h1122, h1124, h730, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, u4ehi2]
                        · linarith only [h0, h1025, h1117, h1122, h1123, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi2]
                      · linarith only [h1025, h1121, h1122, h730, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
                    · linarith only [h0, h1025, h1115, h1121, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi1]
                · linarith only [h1025, h1118, h730, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h1135 | h1135
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1136 | h1136
                  · linarith only [h0, h1025, h1117, h1136, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1138 | h1138
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1139 | h1139
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1140 | h1140
                        · linarith only [h1025, h1115, h1117, h1139, h1140, h730, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                        · linarith only [h0, h1025, h1139, h1140, hc25, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi2]
                      · linarith only [h1025, h1138, h1139, h730, hc24, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
                    · linarith only [h0, h1025, h1115, h1138, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi1]
                · linarith only [h1025, h1135, h730, hlam]
            · linarith only [h0, h1025, h1116, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h1147 | h1147
            · rcases m.htr 0 2 5 (by decide) (by decide) with h1148 | h1148
              · rcases m.htr 0 3 4 (by decide) (by decide) with h1149 | h1149
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1150 | h1150
                  · linarith only [h1025, h1026, h1150, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1152 | h1152
                    · linarith only [h1115, h1147, h1152, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                    · linarith only [h0, h1025, h1152, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
                · linarith only [h1025, h1026, h1115, h1148, h1149, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h1156 | h1156
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1157 | h1157
                  · linarith only [h0, h1025, h1148, h1157, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1159 | h1159
                    · linarith only [h0, h1115, h1159, hc12, hlam, hphi, ht01, u0ehi5]
                    · linarith only [h0, h1025, h1159, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b, u4ehi1]
                · linarith only [h0, h1025, h1115, h1156, hlam]
            · linarith only [h0, h1025, h1147, hlam]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h1164 | h1164
        · rcases m.htr 0 2 3 (by decide) (by decide) with h1165 | h1165
          · rcases m.htr 0 2 4 (by decide) (by decide) with h1166 | h1166
            · rcases m.htr 0 2 5 (by decide) (by decide) with h1167 | h1167
              · rcases m.htr 0 3 4 (by decide) (by decide) with h1168 | h1168
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1169 | h1169
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1170 | h1170
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1171 | h1171
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1172 | h1172
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1173 | h1173
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1174 | h1174
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1175 | h1175
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1176 | h1176
                                · linarith only [h1165, h1176, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi3]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h1178 | h1178
                                  · linarith only [h1165, h1168, h1176, h1178, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1180 | h1180
                                    · linarith only [h1165, h1168, h1176, h1180, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi4]
                                    · linarith only [h1169, h1180, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi2]
                              · linarith only [h1025, h1165, h1168, h1169, h1175, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo1]
                            · linarith only [h1025, h1164, h1173, h1174, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi9]
                          · linarith only [h1164, h1165, h1168, h1173, h730, hlam, hphi, u0ehi9, u0elo1]
                        · linarith only [h1164, h1170, h1172, h730, hc25, hlam, hphi, ht01, ht12, u0ehi9]
                      · linarith only [h1164, h1170, h1171, h730, hc24, hlam, hphi, ht01, ht12, u0ehi9]
                    · linarith only [h0, h1164, h1170, hc23, hlam, hphi, ht01, ht12, u0ehi9]
                  · linarith only [h1025, h1164, h1169, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1190 | h1190
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1191 | h1191
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1192 | h1192
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1193 | h1193
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1194 | h1194
                          · linarith only [h1168, h1191, h1194, h730, hc12, hlam, hphi, ht01, u0ehi5]
                          · linarith only [h1164, h1194, h730, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi9]
                        · linarith only [h0, h1164, h1193, hc25, hlam, hphi, ht01, ht12, u0ehi9]
                      · linarith only [h1164, h1166, h1191, h1192, h730, hlam, hphi, u0ehi9, u0elo1]
                    · linarith only [h0, h1164, h1165, h1191, hlam, hphi, u0ehi9, u0elo1]
                  · linarith only [h1025, h1164, h1190, hlam]
              · linarith only [h0, h1164, h1167, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h1202 | h1202
              · rcases m.htr 0 3 4 (by decide) (by decide) with h1203 | h1203
                · linarith only [h1165, h1166, h1203, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1205 | h1205
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1206 | h1206
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1207 | h1207
                      · linarith only [h1165, h1166, h1207, h730, hc12, hlam, hphi, ht01, u0ehi5]
                      · linarith only [h0, h1164, h1207, hc24, hlam, hphi, ht01, ht12, u0ehi9]
                    · linarith only [h0, h1164, h1165, h1206, hlam, hphi, u0ehi9, u0elo1]
                  · linarith only [h0, h1164, h1166, h1205, hlam]
              · linarith only [h1164, h1165, h1202, h730, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h1213 | h1213
            · rcases m.htr 0 2 5 (by decide) (by decide) with h1214 | h1214
              · rcases m.htr 0 3 4 (by decide) (by decide) with h1215 | h1215
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1216 | h1216
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1217 | h1217
                    · linarith only [h1165, h1213, h1216, h1217, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi4]
                    · linarith only [h0, h1217, hc23, hlam, hphi, ht01, ht12, u0ehi5]
                  · linarith only [h1025, h1164, h1216, hlam]
                · linarith only [h1165, h1213, h1215, hlam]
              · linarith only [h1025, h1164, h1213, h1214, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h1223 | h1223
              · rcases m.htr 0 3 4 (by decide) (by decide) with h1224 | h1224
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1225 | h1225
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1226 | h1226
                    · linarith only [h1165, h1226, hc12, hlam, hphi, ht01, u0ehi6]
                    · linarith only [h0, h1164, h1226, hc23, hlam, hphi, ht01, ht12, u0ehi9]
                  · linarith only [h0, h1164, h1213, h1225, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1230 | h1230
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1231 | h1231
                    · linarith only [h0, h1164, h1165, h1231, hc12, hlam, hphi, ht01, u0ehi9]
                    · linarith only [h0, h1164, h1231, hc23, hlam, hphi, ht01, ht12, u0ehi9]
                  · linarith only [h1164, h1224, h1230, h730, hlam]
              · linarith only [h0, h1164, h1223, hlam]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h1236 | h1236
          · rcases m.htr 0 2 4 (by decide) (by decide) with h1237 | h1237
            · rcases m.htr 0 2 5 (by decide) (by decide) with h1238 | h1238
              · rcases m.htr 0 3 4 (by decide) (by decide) with h1239 | h1239
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1240 | h1240
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1241 | h1241
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1242 | h1242
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1243 | h1243
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1244 | h1244
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1245 | h1245
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1246 | h1246
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h1247 | h1247
                                · linarith only [h1236, h1247, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi3]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h1249 | h1249
                                  · linarith only [h1236, h1239, h1247, h1249, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h1251 | h1251
                                    · linarith only [h1236, h1239, h1247, h1251, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi4]
                                    · linarith only [h1240, h1251, hlam, hphi, ht0b, ht45, ht5b, u0elo3, u4ehi2]
                              · linarith only [h1236, h1239, h1240, h1246, hlam, hphi, ht0b, ht45, ht5b, u0elo1, u4ehi1]
                            · linarith only [h1245, h730, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi5]
                          · linarith only [h1236, h1239, h1244, h730, hlam, hphi, u0ehi5, u0elo1]
                        · linarith only [h0, h1238, h1243, hlam, hphi, u0ehi5, u0elo1]
                      · linarith only [h1241, h1242, h730, hc24, hlam, hphi, ht01, ht12, u0ehi5]
                    · linarith only [h0, h1241, hc23, hlam, hphi, ht01, ht12, u0ehi5]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1260 | h1260
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1261 | h1261
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1262 | h1262
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1263 | h1263
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h1264 | h1264
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h1265 | h1265
                              · linarith only [h1240, h1260, h1263, h1265, hc12, hlam, hphi, ht01, u0ehi8]
                              · linarith only [h1025, h1265, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi5]
                            · linarith only [h1264, h730, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi5]
                          · linarith only [h1236, h1239, h1263, h730, hlam, hphi, u0ehi5, u0elo1]
                        · linarith only [h0, h1238, h1262, hlam, hphi, u0ehi5, u0elo1]
                      · linarith only [h1237, h1260, h1261, h730, hlam, hphi, u0ehi5, u0elo1]
                    · linarith only [h0, h1236, h1260, hlam, hphi, u0ehi5, u0elo1]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1273 | h1273
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1274 | h1274
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1275 | h1275
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1276 | h1276
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1277 | h1277
                          · linarith only [h1239, h1274, h1277, hc12, hlam, hphi, ht01, u0ehi7]
                          · linarith only [h1277, h730, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi5]
                        · linarith only [h0, h1238, h1276, hlam, hphi, u0ehi5, u0elo1]
                      · linarith only [h1237, h1274, h1275, h730, hlam, hphi, u0ehi5, u0elo1]
                    · linarith only [h0, h1236, h1274, hlam, hphi, u0ehi5, u0elo1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1283 | h1283
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1284 | h1284
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1285 | h1285
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h1286 | h1286
                          · linarith only [h1239, h1283, h1286, h730, hc12, hlam, hphi, ht01, u0ehi5]
                          · linarith only [h1286, h730, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi5]
                        · linarith only [h0, h1238, h1285, hlam, hphi, u0ehi5, u0elo1]
                      · linarith only [h1237, h1283, h1284, h730, hlam, hphi, u0ehi5, u0elo1]
                    · linarith only [h0, h1236, h1283, hlam, hphi, u0ehi5, u0elo1]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h1292 | h1292
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1293 | h1293
                  · linarith only [h1236, h1238, h1292, h1293, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1295 | h1295
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1296 | h1296
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1297 | h1297
                        · linarith only [h1237, h1238, h1297, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                        · linarith only [h0, h1297, hc25, hlam, hphi, ht01, ht12, u0ehi5]
                      · linarith only [h1295, h1296, h730, hc24, hlam, hphi, ht01, ht12, u0ehi5]
                    · linarith only [h0, h1236, h1295, hlam, hphi, u0ehi5, u0elo1]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1302 | h1302
                  · linarith only [h1237, h1238, h1302, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1304 | h1304
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1305 | h1305
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h1306 | h1306
                        · linarith only [h1237, h1238, h1306, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                        · linarith only [h0, h1306, hc25, hlam, hphi, ht01, ht12, u0ehi5]
                      · linarith only [h1304, h1305, h730, hc24, hlam, hphi, ht01, ht12, u0ehi5]
                    · linarith only [h0, h1236, h1304, hlam, hphi, u0ehi5, u0elo1]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h1311 | h1311
              · rcases m.htr 0 3 4 (by decide) (by decide) with h1312 | h1312
                · linarith only [h1236, h1237, h1312, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1314 | h1314
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1315 | h1315
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1316 | h1316
                      · linarith only [h1237, h1316, hc12, hlam, hphi, ht01, u0ehi6]
                      · linarith only [h0, h1316, hc24, hlam, hphi, ht01, ht12, u0ehi5]
                    · linarith only [h0, h1236, h1315, hlam, hphi, u0ehi5, u0elo1]
                  · linarith only [h1237, h1311, h1314, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h1321 | h1321
                · linarith only [h1236, h1237, h1321, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1323 | h1323
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1324 | h1324
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1325 | h1325
                      · linarith only [h1236, h1237, h1325, h730, hc12, hlam, hphi, ht01, u0ehi5]
                      · linarith only [h0, h1325, hc24, hlam, hphi, ht01, ht12, u0ehi5]
                    · linarith only [h0, h1236, h1324, hlam, hphi, u0ehi5, u0elo1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1329 | h1329
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h1330 | h1330
                      · linarith only [h1236, h1237, h1330, h730, hc12, hlam, hphi, ht01, u0ehi5]
                      · linarith only [h0, h1330, hc24, hlam, hphi, ht01, ht12, u0ehi5]
                    · linarith only [h0, h1236, h1237, h1323, h1329, hc45, hlam, hphi, ht01, ht12, ht23, ht34, u0ehi5]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h1334 | h1334
            · rcases m.htr 0 2 5 (by decide) (by decide) with h1335 | h1335
              · rcases m.htr 0 3 4 (by decide) (by decide) with h1336 | h1336
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1337 | h1337
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1338 | h1338
                    · linarith only [h1236, h1334, h1338, hc12, hlam, hphi, ht01, ht0b, ht45, ht5b, u4ehi2]
                    · linarith only [h0, h1338, hc23, hlam, hphi, ht01, ht12, u0ehi5]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1341 | h1341
                    · linarith only [h1236, h1341, hc12, hlam, hphi, ht01, u0ehi6]
                    · linarith only [h0, h1341, hc23, hlam, hphi, ht01, ht12, u0ehi5]
                · linarith only [h1236, h1334, h1336, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h1345 | h1345
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1346 | h1346
                  · linarith only [h1334, h1335, h1346, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1348 | h1348
                    · linarith only [h1236, h1348, hc12, hlam, hphi, ht01, u0ehi6]
                    · linarith only [h0, h1348, hc23, hlam, hphi, ht01, ht12, u0ehi5]
                · linarith only [h1236, h1334, h1345, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h1352 | h1352
              · rcases m.htr 0 3 4 (by decide) (by decide) with h1353 | h1353
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1354 | h1354
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1355 | h1355
                    · linarith only [h1236, h1355, hc12, hlam, hphi, ht01, u0ehi6]
                    · linarith only [h0, h1355, hc23, hlam, hphi, ht01, ht12, u0ehi5]
                  · linarith only [h1334, h1352, h1354, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1359 | h1359
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1360 | h1360
                    · linarith only [h1164, h1236, h1352, h1360, hc12, hlam, hphi, ht01, u0ehi5]
                    · linarith only [h0, h1360, hc23, hlam, hphi, ht01, ht12, u0ehi5]
                  · linarith only [h1236, h1352, h1353, h1359, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h1364 | h1364
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1365 | h1365
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1366 | h1366
                    · linarith only [h1236, h1366, hc12, hlam, hphi, ht01, u0ehi6]
                    · linarith only [h0, h1366, hc23, hlam, hphi, ht01, ht12, u0ehi5]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1369 | h1369
                    · linarith only [h0, h1236, h1369, hc12, hlam, hphi, ht01, u0ehi5]
                    · linarith only [h0, h1369, hc23, hlam, hphi, ht01, ht12, u0ehi5]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h1372 | h1372
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1373 | h1373
                    · linarith only [h0, h1236, h1373, hc12, hlam, hphi, ht01, u0ehi5]
                    · linarith only [h0, h1373, hc23, hlam, hphi, ht01, ht12, u0ehi5]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h1376 | h1376
                    · linarith only [h0, h1236, h1376, hc12, hlam, hphi, ht01, u0ehi5]
                    · linarith only [h0, h1376, hc23, hlam, hphi, ht01, ht12, u0ehi5]

end R2N4
