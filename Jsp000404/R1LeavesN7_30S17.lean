import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_30S16

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 9746000 in
set_option maxHeartbeats 9746000 in
theorem r1l7_20_12_13_15_H_L_L_I_L_I_L_I (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig1_7_L_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have h0elo := hb0.1
  have h2bigk := hb2.1
  have h3bigk := hb3.1
  have h5bigk := hb5.1
  have u0elo0 := h0elo (m.d 0 1) (by simp)
  have u0elo1 := h0elo (m.d 0 2) (by simp)
  have u0elo2 := h0elo (m.d 0 3) (by simp)
  have u0elo3 := h0elo (m.d 0 4) (by simp)
  have u0elo4 := h0elo (m.d 0 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 1 4 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 1 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 0 2 3 (by decide) (by decide) with h4 | h4
          · rcases m.htr 0 2 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 0 2 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 0 3 4 (by decide) (by decide) with h7 | h7
                · rcases m.htr 0 3 5 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h9 | h9
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h10 | h10
                      · linarith only [h0, h10, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · linarith only [h0, h10, h4, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h13 | h13
                      · linarith only [h0, h13, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · linarith only [h0, h13, h4, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h16 | h16
                    · linarith only [h16, h7, h8, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h18 | h18
                      · linarith only [h0, h18, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · linarith only [h0, h18, h4, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h21 | h21
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h22 | h22
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h23 | h23
                      · linarith only [h0, h23, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · linarith only [h0, h23, h4, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · linarith only [h21, h22, h7, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h27 | h27
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h28 | h28
                      · linarith only [h0, h28, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · linarith only [h0, h28, h4, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h31 | h31
                      · linarith only [h0, h31, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · linarith only [h0, h31, h4, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h34 | h34
                · rcases m.htr 0 3 5 (by decide) (by decide) with h35 | h35
                  · linarith only [h35, h4, h6, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h37 | h37
                    · linarith only [h34, h37, h4, h6, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h39 | h39
                      · linarith only [h0, h39, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · linarith only [h3, h39, h4, h6, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h42 | h42
                  · linarith only [h34, h42, h5, h6, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h44 | h44
                    · linarith only [h44, h5, h6, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h46 | h46
                      · linarith only [h0, h46, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · linarith only [h3, h4, h46, h6, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h49 | h49
              · rcases m.htr 0 3 4 (by decide) (by decide) with h50 | h50
                · linarith only [h4, h5, h50, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h52 | h52
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h53 | h53
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h54 | h54
                      · linarith only [h0, h54, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · linarith only [h2, h4, h5, h54, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · linarith only [h4, h5, h52, h53, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h58 | h58
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h59 | h59
                      · linarith only [h0, h59, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · linarith only [h2, h4, h5, h59, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · linarith only [h49, h5, h58, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h63 | h63
                · linarith only [h4, h5, h63, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h65 | h65
                  · linarith only [h4, h49, h65, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h67 | h67
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h68 | h68
                      · linarith only [h0, h68, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · linarith only [h2, h4, h49, h67, h68, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h71 | h71
                      · linarith only [h0, h71, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · linarith only [h4, h71, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h74 | h74
            · rcases m.htr 0 2 5 (by decide) (by decide) with h75 | h75
              · rcases m.htr 0 3 4 (by decide) (by decide) with h76 | h76
                · rcases m.htr 0 3 5 (by decide) (by decide) with h77 | h77
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h78 | h78
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h79 | h79
                      · linarith only [h0, h4, h79, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h81 | h81
                        · linarith only [h1, h79, h81, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                        · linarith only [h74, h81, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h84 | h84
                      · linarith only [h0, h4, h84, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h86 | h86
                        · linarith only [h1, h84, h86, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                        · linarith only [h74, h86, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h4, h75, h77, hlam]
                · linarith only [h4, h74, h76, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h91 | h91
                · rcases m.htr 0 3 5 (by decide) (by decide) with h92 | h92
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h93 | h93
                    · linarith only [h74, h75, h93, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h95 | h95
                      · linarith only [h0, h4, h74, h95, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h97 | h97
                        · linarith only [h1, h95, h97, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                        · linarith only [h74, h97, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h100 | h100
                    · linarith only [h100, h4, h74, h92, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h102 | h102
                      · linarith only [h0, h102, h4, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h104 | h104
                        · linarith only [h1, h102, h104, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                        · linarith only [h104, h74, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                · linarith only [h4, h74, h91, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h108 | h108
              · rcases m.htr 0 3 4 (by decide) (by decide) with h109 | h109
                · rcases m.htr 0 3 5 (by decide) (by decide) with h110 | h110
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h111 | h111
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h112 | h112
                      · linarith only [h0, h112, h4, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h114 | h114
                        · linarith only [h1, h108, h112, h114, h74, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h116 | h116
                          · linarith only [h1, h112, h116, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                          · linarith only [h108, h116, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h108, h111, h74, hlam]
                  · linarith only [h108, h109, h110, h74, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h121 | h121
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h122 | h122
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h123 | h123
                      · linarith only [h0, h123, h4, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h125 | h125
                        · linarith only [h1, h123, h125, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h127 | h127
                          · linarith only [h1, h123, h127, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                          · linarith only [h108, h127, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h108, h109, h122, h4, hlam]
                  · linarith only [h108, h121, h4, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h132 | h132
                · rcases m.htr 0 3 5 (by decide) (by decide) with h133 | h133
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h134 | h134
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h135 | h135
                      · linarith only [h0, h135, h4, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h137 | h137
                        · linarith only [h0, h137, h74, hlam]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h139 | h139
                          · linarith only [h0, h108, h139, hlam]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h141 | h141
                            · linarith only [h1, h141, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                            · linarith only [h1, h132, h141, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h144 | h144
                      · linarith only [h0, h132, h144, h4, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h146 | h146
                        · linarith only [h0, h146, h74, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h148 | h148
                          · linarith only [h0, h108, h134, h148, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h150 | h150
                            · linarith only [h1, h150, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                            · linarith only [h132, h150, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h153 | h153
                    · linarith only [h132, h133, h153, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h155 | h155
                      · linarith only [h0, h132, h155, h4, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h157 | h157
                        · linarith only [h1, h155, h157, h74, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h159 | h159
                          · linarith only [h0, h108, h159, hc05, hlam, hphi, ht0b, ht5b, u0elo0]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h161 | h161
                            · linarith only [h1, h161, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                            · linarith only [h132, h161, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h164 | h164
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h165 | h165
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h166 | h166
                      · linarith only [h0, h166, h4, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h168 | h168
                        · linarith only [h0, h132, h164, h168, h74, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h170 | h170
                          · linarith only [h1, h108, h166, h170, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h172 | h172
                            · linarith only [h1, h132, h164, h172, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h174 | h174
                              · linarith only [h172, h174, h2, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                              · linarith only [h164, h174, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                    · linarith only [h132, h164, h165, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h178 | h178
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h179 | h179
                      · linarith only [h0, h179, h4, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h181 | h181
                        · linarith only [h0, h178, h181, h4, h74, hc45, hlam, hphi, ht0b, ht5b, u0elo2]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h183 | h183
                          · linarith only [h1, h108, h179, h183, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h185 | h185
                            · linarith only [h1, h132, h185, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h187 | h187
                              · linarith only [h1, h164, h187, hc05, hlam, hphi, ht0b, ht5b, u0elo0]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h189 | h189
                                · linarith only [h189, h2, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                                · linarith only [h178, h185, h189, h2, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h192 | h192
                      · linarith only [h0, h192, h4, hlam]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h194 | h194
                        · linarith only [h0, h194, h74, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h196 | h196
                          · linarith only [h1, h108, h192, h196, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h198 | h198
                            · linarith only [h1, h132, h198, hlam]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h200 | h200
                              · linarith only [h1, h164, h200, hc05, hlam, hphi, ht0b, ht5b, u0elo0]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h202 | h202
                                · linarith only [h0, h132, h178, h2, h202, h4, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h204 | h204
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h205 | h205
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h206 | h206
                                      · rcases m.htr 3 4 5 (by decide) (by decide) with h207 | h207
                                        · linarith only [h0, h132, h178, h204, h207, h4, hc12, hc23, hlam, hphi]
                                        · linarith only [h0, h132, h206, h207, h4, hc12, hc24, hlam, hphi]
                                      · rcases m.htr 3 4 5 (by decide) (by decide) with h210 | h210
                                        · linarith only [h0, h206, h210, h74, hc12, hc34, hlam, hphi, ht23]
                                        · rcases h2bigk with h212c | h212c | h212c | h212c | h212c | h212c | h212c | h212c | h212c | h212c | h212c | h212c | h212c | h212c | h212c | h212c | h212c | h212c | h212c | h212c | h212c | h212c | h212c | h212c | h212c
                                          · have p212_0 := h212c.1
                                            have p212_1 := h212c.2.1
                                            have p212_2 := h212c.2.2.1
                                            have p212_3 := h212c.2.2.2
                                            linarith only [hlam, p212_0]
                                          · have p212_0 := h212c.1
                                            have p212_1 := h212c.2.1
                                            have p212_2 := h212c.2.2.1
                                            have p212_3 := h212c.2.2.2
                                            linarith only [hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p212_1, u0elo1]
                                          · have p212_0 := h212c.1
                                            have p212_1 := h212c.2.1
                                            have p212_2 := h212c.2.2.1
                                            have p212_3 := h212c.2.2.2
                                            linarith only [h4, hlam, p212_0]
                                          · have p212_0 := h212c.1
                                            have p212_1 := h212c.2.1
                                            have p212_2 := h212c.2.2.1
                                            have p212_3 := h212c.2.2.2
                                            linarith only [h74, hlam, p212_0]
                                          · have p212_0 := h212c.1
                                            have p212_1 := h212c.2.1
                                            have p212_2 := h212c.2.2.1
                                            have p212_3 := h212c.2.2.2
                                            linarith only [h108, hlam, p212_0]
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
                                            linarith only [h192, hlam, p212_0]
                                          · have p212_0 := h212c.1
                                            have p212_1 := h212c.2.1
                                            have p212_2 := h212c.2.2.1
                                            have p212_3 := h212c.2.2.2
                                            linarith only [h194, hlam, p212_0]
                                          · have p212_0 := h212c.1
                                            have p212_1 := h212c.2.1
                                            have p212_2 := h212c.2.2.1
                                            have p212_3 := h212c.2.2.2
                                            linarith only [h196, hlam, p212_0]
                                          · have p212_0 := h212c.1
                                            have p212_1 := h212c.2.1
                                            have p212_2 := h212c.2.2.1
                                            have p212_3 := h212c.2.2.2
                                            rcases p212_3 (m.d 0 2) (by simp) with h223 | h223
                                            · linarith only [h223, hlam, p212_0]
                                            · rcases p212_3 (m.d 1 2) (by simp) with h225 | h225
                                              · linarith only [h192, h225, hlam]
                                              · rcases p212_3 (m.d 2 3) (by simp) with h227 | h227
                                                · rcases p212_3 (m.d 2 4) (by simp) with h228 | h228
                                                  · linarith only [h204, h228, hlam]
                                                  · linarith only [h228, h74, hlam]
                                                · linarith only [h227, hlam, p212_0]
                                          · have p212_0 := h212c.1
                                            have p212_1 := h212c.2.1
                                            have p212_2 := h212c.2.2.1
                                            have p212_3 := h212c.2.2.2
                                            rcases p212_3 (m.d 0 2) (by simp) with h232 | h232
                                            · linarith only [h232, h4, hlam]
                                            · linarith only [h0, h232, hlam]
                                          · have p212_0 := h212c.1
                                            have p212_1 := h212c.2.1
                                            have p212_2 := h212c.2.2.1
                                            have p212_3 := h212c.2.2.2
                                            linarith only [hlam, p212_0]
                                          · have p212_0 := h212c.1
                                            have p212_1 := h212c.2.1
                                            have p212_2 := h212c.2.2.1
                                            have p212_3 := h212c.2.2.2
                                            linarith only [h132, h204, h4, hc02, hc23, hlam, hphi, p212_1]
                                          · have p212_0 := h212c.1
                                            have p212_1 := h212c.2.1
                                            have p212_2 := h212c.2.2.1
                                            have p212_3 := h212c.2.2.2
                                            linarith only [h0, h108, hc12, hc23, hlam, hphi, p212_1]
                                          · have p212_0 := h212c.1
                                            have p212_1 := h212c.2.1
                                            have p212_2 := h212c.2.2.1
                                            have p212_3 := h212c.2.2.2
                                            linarith only [h0, h206, hc12, hc45, hlam, hphi, ht23, ht34, p212_1]
                                          · have p212_0 := h212c.1
                                            have p212_1 := h212c.2.1
                                            have p212_2 := h212c.2.2.1
                                            have p212_3 := h212c.2.2.2
                                            linarith only [h206, hc12, hc45, hlam, hphi, ht23, ht34, p212_1]
                                          · have p212_0 := h212c.1
                                            have p212_1 := h212c.2.1
                                            have p212_2 := h212c.2.2.1
                                            have p212_3 := h212c.2.2.2
                                            linarith only [h204, hlam, p212_1]
                                          · have p212_0 := h212c.1
                                            have p212_1 := h212c.2.1
                                            have p212_2 := h212c.2.2.1
                                            have p212_3 := h212c.2.2.2
                                            linarith only [hlam, p212_0]
                                          · have p212_0 := h212c.1
                                            have p212_1 := h212c.2.1
                                            have p212_2 := h212c.2.2.1
                                            have p212_3 := h212c.2.2.2
                                            linarith only [h206, hlam, p212_1]
                                          · have p212_0 := h212c.1
                                            have p212_1 := h212c.2.1
                                            have p212_2 := h212c.2.2.1
                                            have p212_3 := h212c.2.2.2
                                            rcases p212_3 (m.d 0 2) (by simp) with h243 | h243
                                            · linarith only [h243, hlam, p212_0]
                                            · rcases p212_3 (m.d 1 2) (by simp) with h245 | h245
                                              · linarith only [h196, h245, hlam]
                                              · rcases p212_3 (m.d 2 3) (by simp) with h247 | h247
                                                · rcases p212_3 (m.d 2 4) (by simp) with h248 | h248
                                                  · linarith only [h206, h248, hlam]
                                                  · linarith only [h248, h74, hlam]
                                                · linarith only [h247, h4, hlam]
                                          · have p212_0 := h212c.1
                                            have p212_1 := h212c.2.1
                                            have p212_2 := h212c.2.2.1
                                            have p212_3 := h212c.2.2.2
                                            rcases p212_3 (m.d 0 2) (by simp) with h252 | h252
                                            · linarith only [h108, h252, hlam]
                                            · linarith only [h0, h252, hlam]
                                          · have p212_0 := h212c.1
                                            have p212_1 := h212c.2.1
                                            have p212_2 := h212c.2.2.1
                                            have p212_3 := h212c.2.2.2
                                            linarith only [h205, hlam, p212_1]
                                          · have p212_0 := h212c.1
                                            have p212_1 := h212c.2.1
                                            have p212_2 := h212c.2.2.1
                                            have p212_3 := h212c.2.2.2
                                            linarith only [h0, h74, hc12, hc25, hlam, hphi, p212_1]
                                          · have p212_0 := h212c.1
                                            have p212_1 := h212c.2.1
                                            have p212_2 := h212c.2.2.1
                                            have p212_3 := h212c.2.2.2
                                            linarith only [hlam, p212_0]
                                    · linarith only [h0, h132, h204, h205, h4, hc12, hc35, hlam, hphi, ht23]
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h259 | h259
                                    · linarith only [h0, h164, h204, h259, h4, hc12, hc34, hlam, hphi, ht23]
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h261 | h261
                                      · rcases m.htr 3 4 5 (by decide) (by decide) with h262 | h262
                                        · rcases h2bigk with h263c | h263c | h263c | h263c | h263c | h263c | h263c | h263c | h263c | h263c | h263c | h263c | h263c | h263c | h263c | h263c | h263c | h263c | h263c | h263c | h263c | h263c | h263c | h263c | h263c
                                          · have p263_0 := h263c.1
                                            have p263_1 := h263c.2.1
                                            have p263_2 := h263c.2.2.1
                                            have p263_3 := h263c.2.2.2
                                            linarith only [hlam, p263_0]
                                          · have p263_0 := h263c.1
                                            have p263_1 := h263c.2.1
                                            have p263_2 := h263c.2.2.1
                                            have p263_3 := h263c.2.2.2
                                            linarith only [hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p263_1, u0elo1]
                                          · have p263_0 := h263c.1
                                            have p263_1 := h263c.2.1
                                            have p263_2 := h263c.2.2.1
                                            have p263_3 := h263c.2.2.2
                                            linarith only [h4, hlam, p263_0]
                                          · have p263_0 := h263c.1
                                            have p263_1 := h263c.2.1
                                            have p263_2 := h263c.2.2.1
                                            have p263_3 := h263c.2.2.2
                                            linarith only [h74, hlam, p263_0]
                                          · have p263_0 := h263c.1
                                            have p263_1 := h263c.2.1
                                            have p263_2 := h263c.2.2.1
                                            have p263_3 := h263c.2.2.2
                                            linarith only [h108, hlam, p263_0]
                                          · have p263_0 := h263c.1
                                            have p263_1 := h263c.2.1
                                            have p263_2 := h263c.2.2.1
                                            have p263_3 := h263c.2.2.2
                                            linarith only [h0, hlam, p263_0]
                                          · have p263_0 := h263c.1
                                            have p263_1 := h263c.2.1
                                            have p263_2 := h263c.2.2.1
                                            have p263_3 := h263c.2.2.2
                                            linarith only [hlam, p263_0]
                                          · have p263_0 := h263c.1
                                            have p263_1 := h263c.2.1
                                            have p263_2 := h263c.2.2.1
                                            have p263_3 := h263c.2.2.2
                                            linarith only [h192, hlam, p263_0]
                                          · have p263_0 := h263c.1
                                            have p263_1 := h263c.2.1
                                            have p263_2 := h263c.2.2.1
                                            have p263_3 := h263c.2.2.2
                                            linarith only [h194, hlam, p263_0]
                                          · have p263_0 := h263c.1
                                            have p263_1 := h263c.2.1
                                            have p263_2 := h263c.2.2.1
                                            have p263_3 := h263c.2.2.2
                                            linarith only [h196, hlam, p263_0]
                                          · have p263_0 := h263c.1
                                            have p263_1 := h263c.2.1
                                            have p263_2 := h263c.2.2.1
                                            have p263_3 := h263c.2.2.2
                                            linarith only [h259, h262, hc02, hc34, hlam, hphi, ht23, p263_1]
                                          · have p263_0 := h263c.1
                                            have p263_1 := h263c.2.1
                                            have p263_2 := h263c.2.2.1
                                            have p263_3 := h263c.2.2.2
                                            linarith only [h259, h262, hc12, hc34, hlam, hphi, ht23, p263_1]
                                          · have p263_0 := h263c.1
                                            have p263_1 := h263c.2.1
                                            have p263_2 := h263c.2.2.1
                                            have p263_3 := h263c.2.2.2
                                            linarith only [hlam, p263_0]
                                          · have p263_0 := h263c.1
                                            have p263_1 := h263c.2.1
                                            have p263_2 := h263c.2.2.1
                                            have p263_3 := h263c.2.2.2
                                            linarith only [h204, hlam, p263_0]
                                          · have p263_0 := h263c.1
                                            have p263_1 := h263c.2.1
                                            have p263_2 := h263c.2.2.1
                                            have p263_3 := h263c.2.2.2
                                            linarith only [h259, hlam, p263_0]
                                          · have p263_0 := h263c.1
                                            have p263_1 := h263c.2.1
                                            have p263_2 := h263c.2.2.1
                                            have p263_3 := h263c.2.2.2
                                            rcases p263_3 (m.d 0 2) (by simp) with h279 | h279
                                            · linarith only [h279, hlam, p263_0]
                                            · rcases p263_3 (m.d 1 2) (by simp) with h281 | h281
                                              · linarith only [h194, h281, hlam]
                                              · rcases p263_3 (m.d 2 3) (by simp) with h283 | h283
                                                · linarith only [h204, h283, hlam]
                                                · linarith only [h283, h4, hlam]
                                          · have p263_0 := h263c.1
                                            have p263_1 := h263c.2.1
                                            have p263_2 := h263c.2.2.1
                                            have p263_3 := h263c.2.2.2
                                            rcases p263_3 (m.d 0 2) (by simp) with h286 | h286
                                            · linarith only [h286, h74, hlam]
                                            · linarith only [h0, h286, hlam]
                                          · have p263_0 := h263c.1
                                            have p263_1 := h263c.2.1
                                            have p263_2 := h263c.2.2.1
                                            have p263_3 := h263c.2.2.2
                                            linarith only [h0, h204, h4, hc12, hc34, hlam, hphi, ht23, p263_1]
                                          · have p263_0 := h263c.1
                                            have p263_1 := h263c.2.1
                                            have p263_2 := h263c.2.2.1
                                            have p263_3 := h263c.2.2.2
                                            linarith only [hlam, p263_0]
                                          · have p263_0 := h263c.1
                                            have p263_1 := h263c.2.1
                                            have p263_2 := h263c.2.2.1
                                            have p263_3 := h263c.2.2.2
                                            linarith only [h0, h108, h204, hc12, hc34, hlam, hphi, ht23, p263_1]
                                          · have p263_0 := h263c.1
                                            have p263_1 := h263c.2.1
                                            have p263_2 := h263c.2.2.1
                                            have p263_3 := h263c.2.2.2
                                            rcases p263_3 (m.d 0 2) (by simp) with h292 | h292
                                            · linarith only [h292, hlam, p263_0]
                                            · rcases p263_3 (m.d 1 2) (by simp) with h294 | h294
                                              · linarith only [h196, h294, hlam]
                                              · rcases p263_3 (m.d 2 3) (by simp) with h296 | h296
                                                · linarith only [h259, h296, hlam]
                                                · linarith only [h296, h4, hlam]
                                          · have p263_0 := h263c.1
                                            have p263_1 := h263c.2.1
                                            have p263_2 := h263c.2.2.1
                                            have p263_3 := h263c.2.2.2
                                            rcases p263_3 (m.d 0 2) (by simp) with h299 | h299
                                            · linarith only [h108, h299, hlam]
                                            · linarith only [h0, h299, hlam]
                                          · have p263_0 := h263c.1
                                            have p263_1 := h263c.2.1
                                            have p263_2 := h263c.2.2.1
                                            have p263_3 := h263c.2.2.2
                                            linarith only [h0, h4, hc12, hc25, hlam, hphi, p263_1]
                                          · have p263_0 := h263c.1
                                            have p263_1 := h263c.2.1
                                            have p263_2 := h263c.2.2.1
                                            have p263_3 := h263c.2.2.2
                                            linarith only [h261, hlam, p263_0]
                                          · have p263_0 := h263c.1
                                            have p263_1 := h263c.2.1
                                            have p263_2 := h263c.2.2.1
                                            have p263_3 := h263c.2.2.2
                                            linarith only [hlam, p263_0]
                                        · linarith only [h204, h261, h262, hlam]
                                      · rcases m.htr 3 4 5 (by decide) (by decide) with h306 | h306
                                        · linarith only [h0, h204, h261, h306, h4, hc12, hc34, hlam, hphi, ht23]
                                        · linarith only [h0, h204, h306, h4, hc12, hc45, hlam, hphi, ht23, ht34]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h309 | h309
          · rcases m.htr 0 2 4 (by decide) (by decide) with h310 | h310
            · rcases m.htr 0 2 5 (by decide) (by decide) with h311 | h311
              · linarith only [h0, h3, h311, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h313 | h313
                · rcases m.htr 0 3 5 (by decide) (by decide) with h314 | h314
                  · linarith only [h0, h3, h309, h314, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h316 | h316
                    · linarith only [h0, h3, h309, h313, h316, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h318 | h318
                      · linarith only [h0, h318, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · linarith only [h309, h318, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h321 | h321
                  · linarith only [h1, h3, h321, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h323 | h323
                    · linarith only [h0, h3, h310, h323, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h325 | h325
                      · linarith only [h0, h325, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · linarith only [h0, h3, h309, h325, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo4]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h328 | h328
              · linarith only [h2, h3, h310, h328, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h330 | h330
                · linarith only [h309, h310, h330, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h332 | h332
                  · linarith only [h2, h3, h309, h310, h332, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h334 | h334
                    · linarith only [h2, h3, h334, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h336 | h336
                      · linarith only [h0, h3, h336, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo4]
                      · linarith only [h2, h3, h309, h310, h336, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo4]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h339 | h339
            · rcases m.htr 0 2 5 (by decide) (by decide) with h340 | h340
              · linarith only [h0, h3, h340, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h342 | h342
                · rcases m.htr 0 3 5 (by decide) (by decide) with h343 | h343
                  · linarith only [h1, h3, h343, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h345 | h345
                    · linarith only [h1, h3, h309, h339, h345, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h347 | h347
                      · linarith only [h0, h309, h347, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h349 | h349
                        · linarith only [h1, h3, h347, h349, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo4]
                        · linarith only [h339, h349, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                · linarith only [h309, h339, h342, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h353 | h353
              · linarith only [h1, h3, h309, h353, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h355 | h355
                · rcases m.htr 0 3 5 (by decide) (by decide) with h356 | h356
                  · linarith only [h1, h3, h356, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h358 | h358
                    · linarith only [h1, h3, h355, h358, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h360 | h360
                      · linarith only [h0, h3, h309, h360, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo4]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h362 | h362
                        · linarith only [h0, h3, h339, h362, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo4]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h364 | h364
                          · linarith only [h1, h3, h353, h360, h364, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo4]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h366 | h366
                            · linarith only [h1, h3, h366, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo4]
                            · linarith only [h1, h3, h355, h366, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo4]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h369 | h369
                  · linarith only [h2, h3, h355, h369, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h371 | h371
                    · linarith only [h2, h3, h371, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h373 | h373
                      · linarith only [h0, h3, h309, h373, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo4]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h375 | h375
                        · linarith only [h0, h3, h339, h375, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo4]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h377 | h377
                          · linarith only [h1, h3, h373, h377, hc25, hlam, hphi, ht0b, ht5b, u0elo4]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h379 | h379
                            · linarith only [h1, h3, h309, h355, h379, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo4]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h381 | h381
                              · linarith only [h0, h1, h3, h355, h369, h381, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h383 | h383
                                · linarith only [h2, h309, h355, h371, h383, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h385 | h385
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h386 | h386
                                    · linarith only [h0, h3, h381, h386, hc12, hc23, hlam, hphi]
                                    · linarith only [h0, h309, h355, h385, h386, hc12, hc35, hlam, hphi, ht23]
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h389 | h389
                                    · linarith only [h0, h309, h369, h385, h389, hc12, hc34, hlam, hphi, ht23]
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h391 | h391
                                      · linarith only [h2, h3, h373, h379, h383, h391, hc12, hc24, hlam, hphi]
                                      · rcases m.htr 3 4 5 (by decide) (by decide) with h393 | h393
                                        · linarith only [h0, h309, h385, h391, h393, hc12, hc34, hlam, hphi, ht23]
                                        · linarith only [h0, h309, h385, h393, hc12, hc45, hlam, hphi, ht23, ht34]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h396 | h396
        · rcases m.htr 0 2 3 (by decide) (by decide) with h397 | h397
          · rcases m.htr 0 2 4 (by decide) (by decide) with h398 | h398
            · linarith only [h0, h2, h398, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h400 | h400
              · rcases m.htr 0 3 4 (by decide) (by decide) with h401 | h401
                · linarith only [h1, h2, h401, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h403 | h403
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h404 | h404
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h405 | h405
                      · linarith only [h0, h405, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · linarith only [h0, h2, h397, h405, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3]
                    · linarith only [h0, h2, h397, h403, h404, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h409 | h409
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h410 | h410
                      · linarith only [h0, h2, h410, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                      · linarith only [h0, h2, h397, h410, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3]
                    · linarith only [h0, h2, h400, h409, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h414 | h414
                · linarith only [h1, h2, h414, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h416 | h416
                  · linarith only [h397, h400, h416, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h418 | h418
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h419 | h419
                      · linarith only [h0, h2, h419, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                      · linarith only [h2, h396, h397, h400, h419, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3]
                    · linarith only [h2, h396, h418, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h423 | h423
            · linarith only [h0, h2, h423, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h425 | h425
              · rcases m.htr 0 3 4 (by decide) (by decide) with h426 | h426
                · linarith only [h1, h2, h426, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h428 | h428
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h429 | h429
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h430 | h430
                      · linarith only [h0, h2, h397, h430, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h432 | h432
                        · linarith only [h1, h2, h423, h425, h430, h432, hc25, hlam, hphi, ht0b, ht5b, u0elo3]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h434 | h434
                          · linarith only [h1, h2, h430, h434, hc25, hlam, hphi, ht0b, ht5b, u0elo3]
                          · linarith only [h425, h434, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h1, h2, h397, h425, h429, hlam]
                  · linarith only [h397, h425, h428, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h439 | h439
                · linarith only [h1, h2, h439, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h441 | h441
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h442 | h442
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h443 | h443
                      · linarith only [h0, h2, h443, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h445 | h445
                        · linarith only [h1, h2, h423, h443, h445, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h447 | h447
                          · linarith only [h0, h2, h425, h447, hc05, hlam, hphi, ht0b, ht5b, u0elo3]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h449 | h449
                            · linarith only [h1, h2, h439, h449, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h451 | h451
                              · linarith only [h1, h2, h451, hc35, hlam, hphi, ht0b, ht5b, u0elo3]
                              · linarith only [h441, h443, h451, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                    · linarith only [h2, h396, h442, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h455 | h455
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h456 | h456
                      · linarith only [h0, h397, h456, hlam]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h458 | h458
                        · linarith only [h1, h456, h458, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h460 | h460
                          · linarith only [h0, h425, h460, hlam]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h462 | h462
                            · linarith only [h1, h439, h462, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h464 | h464
                              · linarith only [h1, h441, h464, hlam]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h466 | h466
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h467 | h467
                                  · linarith only [h2, h396, h456, h462, h464, h467, hc12, hc23, hlam, hphi]
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h469 | h469
                                    · linarith only [h1, h441, h456, h467, h469, hc12, hc34, hlam, hphi, ht23]
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h471 | h471
                                      · rcases m.htr 3 4 5 (by decide) (by decide) with h472 | h472
                                        · rcases h2bigk with h473c | h473c | h473c | h473c | h473c | h473c | h473c | h473c | h473c | h473c | h473c | h473c | h473c | h473c | h473c | h473c | h473c | h473c | h473c | h473c | h473c | h473c | h473c | h473c | h473c
                                          · have p473_0 := h473c.1
                                            have p473_1 := h473c.2.1
                                            have p473_2 := h473c.2.2.1
                                            have p473_3 := h473c.2.2.2
                                            linarith only [hlam, p473_0]
                                          · have p473_0 := h473c.1
                                            have p473_1 := h473c.2.1
                                            have p473_2 := h473c.2.2.1
                                            have p473_3 := h473c.2.2.2
                                            linarith only [hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p473_1, u0elo1]
                                          · have p473_0 := h473c.1
                                            have p473_1 := h473c.2.1
                                            have p473_2 := h473c.2.2.1
                                            have p473_3 := h473c.2.2.2
                                            linarith only [h397, hlam, p473_0]
                                          · have p473_0 := h473c.1
                                            have p473_1 := h473c.2.1
                                            have p473_2 := h473c.2.2.1
                                            have p473_3 := h473c.2.2.2
                                            linarith only [h423, hlam, p473_0]
                                          · have p473_0 := h473c.1
                                            have p473_1 := h473c.2.1
                                            have p473_2 := h473c.2.2.1
                                            have p473_3 := h473c.2.2.2
                                            linarith only [h425, hlam, p473_0]
                                          · have p473_0 := h473c.1
                                            have p473_1 := h473c.2.1
                                            have p473_2 := h473c.2.2.1
                                            have p473_3 := h473c.2.2.2
                                            linarith only [h0, hlam, p473_0]
                                          · have p473_0 := h473c.1
                                            have p473_1 := h473c.2.1
                                            have p473_2 := h473c.2.2.1
                                            have p473_3 := h473c.2.2.2
                                            linarith only [hlam, p473_0]
                                          · have p473_0 := h473c.1
                                            have p473_1 := h473c.2.1
                                            have p473_2 := h473c.2.2.1
                                            have p473_3 := h473c.2.2.2
                                            linarith only [h456, hlam, p473_0]
                                          · have p473_0 := h473c.1
                                            have p473_1 := h473c.2.1
                                            have p473_2 := h473c.2.2.1
                                            have p473_3 := h473c.2.2.2
                                            linarith only [h458, hlam, p473_0]
                                          · have p473_0 := h473c.1
                                            have p473_1 := h473c.2.1
                                            have p473_2 := h473c.2.2.1
                                            have p473_3 := h473c.2.2.2
                                            linarith only [h460, hlam, p473_0]
                                          · have p473_0 := h473c.1
                                            have p473_1 := h473c.2.1
                                            have p473_2 := h473c.2.2.1
                                            have p473_3 := h473c.2.2.2
                                            linarith only [h469, h472, hc02, hc34, hlam, hphi, ht23, p473_1]
                                          · have p473_0 := h473c.1
                                            have p473_1 := h473c.2.1
                                            have p473_2 := h473c.2.2.1
                                            have p473_3 := h473c.2.2.2
                                            linarith only [h469, h472, hc12, hc34, hlam, hphi, ht23, p473_1]
                                          · have p473_0 := h473c.1
                                            have p473_1 := h473c.2.1
                                            have p473_2 := h473c.2.2.1
                                            have p473_3 := h473c.2.2.2
                                            linarith only [hlam, p473_0]
                                          · have p473_0 := h473c.1
                                            have p473_1 := h473c.2.1
                                            have p473_2 := h473c.2.2.1
                                            have p473_3 := h473c.2.2.2
                                            linarith only [h467, hlam, p473_0]
                                          · have p473_0 := h473c.1
                                            have p473_1 := h473c.2.1
                                            have p473_2 := h473c.2.2.1
                                            have p473_3 := h473c.2.2.2
                                            linarith only [h469, hlam, p473_0]
                                          · have p473_0 := h473c.1
                                            have p473_1 := h473c.2.1
                                            have p473_2 := h473c.2.2.1
                                            have p473_3 := h473c.2.2.2
                                            rcases p473_3 (m.d 0 2) (by simp) with h489 | h489
                                            · linarith only [h489, hlam, p473_0]
                                            · rcases p473_3 (m.d 1 2) (by simp) with h491 | h491
                                              · linarith only [h458, h491, hlam]
                                              · rcases p473_3 (m.d 2 3) (by simp) with h493 | h493
                                                · linarith only [h467, h493, hlam]
                                                · linarith only [h397, h493, hlam]
                                          · have p473_0 := h473c.1
                                            have p473_1 := h473c.2.1
                                            have p473_2 := h473c.2.2.1
                                            have p473_3 := h473c.2.2.2
                                            rcases p473_3 (m.d 0 2) (by simp) with h496 | h496
                                            · linarith only [h423, h496, hlam]
                                            · linarith only [h0, h496, hlam]
                                          · have p473_0 := h473c.1
                                            have p473_1 := h473c.2.1
                                            have p473_2 := h473c.2.2.1
                                            have p473_3 := h473c.2.2.2
                                            linarith only [h0, h397, hc12, hc24, hlam, hphi, p473_1]
                                          · have p473_0 := h473c.1
                                            have p473_1 := h473c.2.1
                                            have p473_2 := h473c.2.2.1
                                            have p473_3 := h473c.2.2.2
                                            linarith only [hlam, p473_0]
                                          · have p473_0 := h473c.1
                                            have p473_1 := h473c.2.1
                                            have p473_2 := h473c.2.2.1
                                            have p473_3 := h473c.2.2.2
                                            linarith only [h0, h397, h467, h469, hc12, hc34, hlam, hphi, ht23, p473_1]
                                          · have p473_0 := h473c.1
                                            have p473_1 := h473c.2.1
                                            have p473_2 := h473c.2.2.1
                                            have p473_3 := h473c.2.2.2
                                            rcases p473_3 (m.d 0 2) (by simp) with h502 | h502
                                            · linarith only [h502, hlam, p473_0]
                                            · rcases p473_3 (m.d 1 2) (by simp) with h504 | h504
                                              · linarith only [h460, h504, hlam]
                                              · rcases p473_3 (m.d 2 3) (by simp) with h506 | h506
                                                · linarith only [h469, h506, hlam]
                                                · linarith only [h397, h506, hlam]
                                          · have p473_0 := h473c.1
                                            have p473_1 := h473c.2.1
                                            have p473_2 := h473c.2.2.1
                                            have p473_3 := h473c.2.2.2
                                            rcases p473_3 (m.d 0 2) (by simp) with h509 | h509
                                            · linarith only [h425, h509, hlam]
                                            · linarith only [h0, h509, hlam]
                                          · have p473_0 := h473c.1
                                            have p473_1 := h473c.2.1
                                            have p473_2 := h473c.2.2.1
                                            have p473_3 := h473c.2.2.2
                                            linarith only [h0, h397, hc12, hc25, hlam, hphi, p473_1]
                                          · have p473_0 := h473c.1
                                            have p473_1 := h473c.2.1
                                            have p473_2 := h473c.2.2.1
                                            have p473_3 := h473c.2.2.2
                                            linarith only [h471, hlam, p473_0]
                                          · have p473_0 := h473c.1
                                            have p473_1 := h473c.2.1
                                            have p473_2 := h473c.2.2.1
                                            have p473_3 := h473c.2.2.2
                                            linarith only [hlam, p473_0]
                                        · linarith only [h396, h466, h467, h472, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                                      · linarith only [h2, h396, h458, h466, h471, hlam]
                                · linarith only [h2, h396, h456, h464, h466, hc12, hc45, hlam, hphi, ht23, ht34]
                    · linarith only [h2, h396, h455, hlam]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h519 | h519
          · rcases m.htr 0 2 4 (by decide) (by decide) with h520 | h520
            · linarith only [h0, h2, h520, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h522 | h522
              · linarith only [h0, h396, h522, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h524 | h524
                · linarith only [h1, h2, h524, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h526 | h526
                  · linarith only [h0, h396, h519, h526, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h528 | h528
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h529 | h529
                      · linarith only [h0, h529, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · linarith only [h0, h396, h519, h528, h529, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h532 | h532
                      · linarith only [h0, h532, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · linarith only [h0, h2, h519, h528, h532, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo4]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h535 | h535
            · linarith only [h1, h2, h519, h535, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h537 | h537
              · linarith only [h1, h396, h519, h537, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h539 | h539
                · linarith only [h1, h2, h539, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h541 | h541
                  · linarith only [h1, h396, h541, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h543 | h543
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h544 | h544
                      · linarith only [h0, h396, h519, h543, h544, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h546 | h546
                        · linarith only [h1, h396, h535, h543, h544, h546, hlam]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h548 | h548
                          · linarith only [h1, h396, h537, h543, h544, h548, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h550 | h550
                            · linarith only [h1, h396, h539, h543, h550, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h552 | h552
                              · linarith only [h1, h396, h541, h552, hlam]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h554 | h554
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h555 | h555
                                  · linarith only [h0, h396, h550, h554, h555, hc12, hc23, hlam, hphi]
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h557 | h557
                                    · linarith only [h1, h396, h544, h552, h555, h557, hc12, hc34, hlam, hphi, ht23]
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h559 | h559
                                      · rcases m.htr 3 4 5 (by decide) (by decide) with h560 | h560
                                        · rcases h2bigk with h561c | h561c | h561c | h561c | h561c | h561c | h561c | h561c | h561c | h561c | h561c | h561c | h561c | h561c | h561c | h561c | h561c | h561c | h561c | h561c | h561c | h561c | h561c | h561c | h561c
                                          · have p561_0 := h561c.1
                                            have p561_1 := h561c.2.1
                                            have p561_2 := h561c.2.2.1
                                            have p561_3 := h561c.2.2.2
                                            linarith only [hlam, p561_0]
                                          · have p561_0 := h561c.1
                                            have p561_1 := h561c.2.1
                                            have p561_2 := h561c.2.2.1
                                            have p561_3 := h561c.2.2.2
                                            linarith only [hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p561_1, u0elo1]
                                          · have p561_0 := h561c.1
                                            have p561_1 := h561c.2.1
                                            have p561_2 := h561c.2.2.1
                                            have p561_3 := h561c.2.2.2
                                            linarith only [h519, hlam, p561_0]
                                          · have p561_0 := h561c.1
                                            have p561_1 := h561c.2.1
                                            have p561_2 := h561c.2.2.1
                                            have p561_3 := h561c.2.2.2
                                            linarith only [h535, hlam, p561_0]
                                          · have p561_0 := h561c.1
                                            have p561_1 := h561c.2.1
                                            have p561_2 := h561c.2.2.1
                                            have p561_3 := h561c.2.2.2
                                            linarith only [h537, hlam, p561_0]
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
                                            linarith only [h544, hlam, p561_0]
                                          · have p561_0 := h561c.1
                                            have p561_1 := h561c.2.1
                                            have p561_2 := h561c.2.2.1
                                            have p561_3 := h561c.2.2.2
                                            linarith only [h546, hlam, p561_0]
                                          · have p561_0 := h561c.1
                                            have p561_1 := h561c.2.1
                                            have p561_2 := h561c.2.2.1
                                            have p561_3 := h561c.2.2.2
                                            linarith only [h548, hlam, p561_0]
                                          · have p561_0 := h561c.1
                                            have p561_1 := h561c.2.1
                                            have p561_2 := h561c.2.2.1
                                            have p561_3 := h561c.2.2.2
                                            linarith only [h557, h560, hc02, hc34, hlam, hphi, ht23, p561_1]
                                          · have p561_0 := h561c.1
                                            have p561_1 := h561c.2.1
                                            have p561_2 := h561c.2.2.1
                                            have p561_3 := h561c.2.2.2
                                            linarith only [h557, h560, hc12, hc34, hlam, hphi, ht23, p561_1]
                                          · have p561_0 := h561c.1
                                            have p561_1 := h561c.2.1
                                            have p561_2 := h561c.2.2.1
                                            have p561_3 := h561c.2.2.2
                                            linarith only [hlam, p561_0]
                                          · have p561_0 := h561c.1
                                            have p561_1 := h561c.2.1
                                            have p561_2 := h561c.2.2.1
                                            have p561_3 := h561c.2.2.2
                                            linarith only [h555, hlam, p561_0]
                                          · have p561_0 := h561c.1
                                            have p561_1 := h561c.2.1
                                            have p561_2 := h561c.2.2.1
                                            have p561_3 := h561c.2.2.2
                                            linarith only [h557, hlam, p561_0]
                                          · have p561_0 := h561c.1
                                            have p561_1 := h561c.2.1
                                            have p561_2 := h561c.2.2.1
                                            have p561_3 := h561c.2.2.2
                                            rcases p561_3 (m.d 0 2) (by simp) with h577 | h577
                                            · linarith only [h577, hlam, p561_0]
                                            · rcases p561_3 (m.d 1 2) (by simp) with h579 | h579
                                              · linarith only [h546, h579, hlam]
                                              · rcases p561_3 (m.d 2 3) (by simp) with h581 | h581
                                                · linarith only [h555, h581, hlam]
                                                · linarith only [h519, h581, hlam]
                                          · have p561_0 := h561c.1
                                            have p561_1 := h561c.2.1
                                            have p561_2 := h561c.2.2.1
                                            have p561_3 := h561c.2.2.2
                                            rcases p561_3 (m.d 0 2) (by simp) with h584 | h584
                                            · linarith only [h535, h584, hlam]
                                            · linarith only [h0, h584, hlam]
                                          · have p561_0 := h561c.1
                                            have p561_1 := h561c.2.1
                                            have p561_2 := h561c.2.2.1
                                            have p561_3 := h561c.2.2.2
                                            linarith only [h0, h519, hc12, hc24, hlam, hphi, p561_1]
                                          · have p561_0 := h561c.1
                                            have p561_1 := h561c.2.1
                                            have p561_2 := h561c.2.2.1
                                            have p561_3 := h561c.2.2.2
                                            linarith only [hlam, p561_0]
                                          · have p561_0 := h561c.1
                                            have p561_1 := h561c.2.1
                                            have p561_2 := h561c.2.2.1
                                            have p561_3 := h561c.2.2.2
                                            linarith only [h1, h396, h544, h548, h555, hc12, hc34, hlam, hphi, ht23, p561_1]
                                          · have p561_0 := h561c.1
                                            have p561_1 := h561c.2.1
                                            have p561_2 := h561c.2.2.1
                                            have p561_3 := h561c.2.2.2
                                            rcases p561_3 (m.d 0 2) (by simp) with h590 | h590
                                            · linarith only [h590, hlam, p561_0]
                                            · rcases p561_3 (m.d 1 2) (by simp) with h592 | h592
                                              · linarith only [h548, h592, hlam]
                                              · rcases p561_3 (m.d 2 3) (by simp) with h594 | h594
                                                · linarith only [h557, h594, hlam]
                                                · linarith only [h519, h594, hlam]
                                          · have p561_0 := h561c.1
                                            have p561_1 := h561c.2.1
                                            have p561_2 := h561c.2.2.1
                                            have p561_3 := h561c.2.2.2
                                            rcases p561_3 (m.d 0 2) (by simp) with h597 | h597
                                            · linarith only [h537, h597, hlam]
                                            · linarith only [h0, h597, hlam]
                                          · have p561_0 := h561c.1
                                            have p561_1 := h561c.2.1
                                            have p561_2 := h561c.2.2.1
                                            have p561_3 := h561c.2.2.2
                                            linarith only [h0, h519, hc12, hc25, hlam, hphi, p561_1]
                                          · have p561_0 := h561c.1
                                            have p561_1 := h561c.2.1
                                            have p561_2 := h561c.2.2.1
                                            have p561_3 := h561c.2.2.2
                                            linarith only [h559, hlam, p561_0]
                                          · have p561_0 := h561c.1
                                            have p561_1 := h561c.2.1
                                            have p561_2 := h561c.2.2.1
                                            have p561_3 := h561c.2.2.2
                                            linarith only [hlam, p561_0]
                                        · linarith only [h543, h555, h560, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                                      · linarith only [h1, h396, h543, h544, h546, h554, h559, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3]
                                · linarith only [h543, h554, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h606 | h606
                      · linarith only [h0, h519, h606, hlam]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h608 | h608
                        · linarith only [h0, h535, h608, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h610 | h610
                          · linarith only [h1, h2, h543, h606, h610, hc25, hlam, hphi, ht0b, ht5b, u0elo4]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h612 | h612
                            · linarith only [h1, h2, h539, h543, h612, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo4]
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h614 | h614
                              · linarith only [h1, h2, h543, h614, hc35, hlam, hphi, ht0b, ht5b, u0elo4]
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h616 | h616
                                · linarith only [h1, h2, h543, h606, h608, h616, hc12, hc24, hlam, hphi]
                                · linarith only [h1, h2, h606, h616, hc12, hc45, hlam, hphi, ht23, ht34]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h619 | h619
      · rcases m.htr 0 1 5 (by decide) (by decide) with h620 | h620
        · rcases m.htr 0 2 3 (by decide) (by decide) with h621 | h621
          · linarith only [h0, h1, h621, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h623 | h623
            · rcases m.htr 0 2 5 (by decide) (by decide) with h624 | h624
              · rcases m.htr 0 3 4 (by decide) (by decide) with h625 | h625
                · rcases m.htr 0 3 5 (by decide) (by decide) with h626 | h626
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h627 | h627
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h628 | h628
                      · linarith only [h0, h621, h628, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h630 | h630
                        · linarith only [h0, h1, h630, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                        · linarith only [h623, h630, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h633 | h633
                      · linarith only [h0, h1, h621, h633, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h635 | h635
                        · linarith only [h0, h1, h635, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                        · linarith only [h623, h635, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h1, h620, h626, hlam]
                · linarith only [h1, h619, h625, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h640 | h640
                · rcases m.htr 0 3 5 (by decide) (by decide) with h641 | h641
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h642 | h642
                    · linarith only [h623, h624, h642, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h644 | h644
                      · linarith only [h0, h621, h623, h644, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h646 | h646
                        · linarith only [h0, h1, h646, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                        · linarith only [h623, h646, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h1, h620, h641, hlam]
                · linarith only [h1, h620, h623, h624, h640, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h651 | h651
              · rcases m.htr 0 3 4 (by decide) (by decide) with h652 | h652
                · rcases m.htr 0 3 5 (by decide) (by decide) with h653 | h653
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h654 | h654
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h655 | h655
                      · linarith only [h0, h1, h621, h655, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h657 | h657
                        · linarith only [h0, h1, h623, h651, h657, hc25, hlam, hphi, ht0b, ht5b, u0elo2]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h659 | h659
                          · linarith only [h1, h619, h657, h659, hc25, hlam, hphi, ht0b, ht5b, u0elo2]
                          · linarith only [h651, h659, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h623, h651, h654, hlam]
                  · linarith only [h1, h619, h623, h651, h653, hlam]
                · linarith only [h1, h619, h652, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h665 | h665
                · rcases m.htr 0 3 5 (by decide) (by decide) with h666 | h666
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h667 | h667
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h668 | h668
                      · linarith only [h0, h1, h621, h668, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h670 | h670
                        · linarith only [h0, h623, h667, h670, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h672 | h672
                          · linarith only [h1, h619, h651, h670, h672, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h674 | h674
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h675 | h675
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h676 | h676
                                · linarith only [h1, h619, h676, hc45, hlam, hphi, ht0b, ht5b, u0elo2]
                                · linarith only [h667, h676, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                              · linarith only [h0, h1, h675, hc12, hc35, hlam, hphi, ht23]
                            · linarith only [h0, h1, h674, hc12, hc34, hlam, hphi, ht23]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h681 | h681
                      · linarith only [h0, h681, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h683 | h683
                        · linarith only [h0, h623, h683, hlam]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h685 | h685
                          · linarith only [h0, h651, h685, hlam]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h687 | h687
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h688 | h688
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h689 | h689
                                · linarith only [h619, h667, h689, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h691 | h691
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h692 | h692
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h693 | h693
                                      · rcases m.htr 3 4 5 (by decide) (by decide) with h694 | h694
                                        · linarith only [h619, h667, h687, h694, hlam]
                                        · rcases h2bigk with h696c | h696c | h696c | h696c | h696c | h696c | h696c | h696c | h696c | h696c | h696c | h696c | h696c | h696c | h696c | h696c | h696c | h696c | h696c | h696c | h696c | h696c | h696c | h696c | h696c
                                          · have p696_0 := h696c.1
                                            have p696_1 := h696c.2.1
                                            have p696_2 := h696c.2.2.1
                                            have p696_3 := h696c.2.2.2
                                            linarith only [hlam, p696_0]
                                          · have p696_0 := h696c.1
                                            have p696_1 := h696c.2.1
                                            have p696_2 := h696c.2.2.1
                                            have p696_3 := h696c.2.2.2
                                            linarith only [hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p696_1, u0elo1]
                                          · have p696_0 := h696c.1
                                            have p696_1 := h696c.2.1
                                            have p696_2 := h696c.2.2.1
                                            have p696_3 := h696c.2.2.2
                                            linarith only [h621, hlam, p696_0]
                                          · have p696_0 := h696c.1
                                            have p696_1 := h696c.2.1
                                            have p696_2 := h696c.2.2.1
                                            have p696_3 := h696c.2.2.2
                                            linarith only [h623, hlam, p696_0]
                                          · have p696_0 := h696c.1
                                            have p696_1 := h696c.2.1
                                            have p696_2 := h696c.2.2.1
                                            have p696_3 := h696c.2.2.2
                                            linarith only [h651, hlam, p696_0]
                                          · have p696_0 := h696c.1
                                            have p696_1 := h696c.2.1
                                            have p696_2 := h696c.2.2.1
                                            have p696_3 := h696c.2.2.2
                                            linarith only [h0, hlam, p696_0]
                                          · have p696_0 := h696c.1
                                            have p696_1 := h696c.2.1
                                            have p696_2 := h696c.2.2.1
                                            have p696_3 := h696c.2.2.2
                                            linarith only [hlam, p696_0]
                                          · have p696_0 := h696c.1
                                            have p696_1 := h696c.2.1
                                            have p696_2 := h696c.2.2.1
                                            have p696_3 := h696c.2.2.2
                                            linarith only [h681, hlam, p696_0]
                                          · have p696_0 := h696c.1
                                            have p696_1 := h696c.2.1
                                            have p696_2 := h696c.2.2.1
                                            have p696_3 := h696c.2.2.2
                                            linarith only [h683, hlam, p696_0]
                                          · have p696_0 := h696c.1
                                            have p696_1 := h696c.2.1
                                            have p696_2 := h696c.2.2.1
                                            have p696_3 := h696c.2.2.2
                                            linarith only [h685, hlam, p696_0]
                                          · have p696_0 := h696c.1
                                            have p696_1 := h696c.2.1
                                            have p696_2 := h696c.2.2.1
                                            have p696_3 := h696c.2.2.2
                                            rcases p696_3 (m.d 0 2) (by simp) with h707 | h707
                                            · linarith only [h707, hlam, p696_0]
                                            · rcases p696_3 (m.d 1 2) (by simp) with h709 | h709
                                              · linarith only [h681, h709, hlam]
                                              · rcases p696_3 (m.d 2 3) (by simp) with h711 | h711
                                                · rcases p696_3 (m.d 2 4) (by simp) with h712 | h712
                                                  · linarith only [h691, h712, hlam]
                                                  · linarith only [h623, h712, hlam]
                                                · linarith only [h711, hlam, p696_0]
                                          · have p696_0 := h696c.1
                                            have p696_1 := h696c.2.1
                                            have p696_2 := h696c.2.2.1
                                            have p696_3 := h696c.2.2.2
                                            rcases p696_3 (m.d 0 2) (by simp) with h716 | h716
                                            · linarith only [h621, h716, hlam]
                                            · linarith only [h0, h716, hlam]
                                          · have p696_0 := h696c.1
                                            have p696_1 := h696c.2.1
                                            have p696_2 := h696c.2.2.1
                                            have p696_3 := h696c.2.2.2
                                            linarith only [hlam, p696_0]
                                          · have p696_0 := h696c.1
                                            have p696_1 := h696c.2.1
                                            have p696_2 := h696c.2.2.1
                                            have p696_3 := h696c.2.2.2
                                            linarith only [h619, h667, h683, h693, hc12, hc23, hlam, hphi, p696_1]
                                          · have p696_0 := h696c.1
                                            have p696_1 := h696c.2.1
                                            have p696_2 := h696c.2.2.1
                                            have p696_3 := h696c.2.2.2
                                            linarith only [h619, h667, h683, h693, hc12, hc23, hlam, hphi, p696_1]
                                          · have p696_0 := h696c.1
                                            have p696_1 := h696c.2.1
                                            have p696_2 := h696c.2.2.1
                                            have p696_3 := h696c.2.2.2
                                            rcases p696_3 (m.d 0 2) (by simp) with h722 | h722
                                            · linarith only [h722, hlam, p696_0]
                                            · rcases p696_3 (m.d 1 2) (by simp) with h724 | h724
                                              · linarith only [h683, h724, hlam]
                                              · rcases p696_3 (m.d 2 3) (by simp) with h726 | h726
                                                · rcases p696_3 (m.d 2 4) (by simp) with h727 | h727
                                                  · rcases p696_3 (m.d 2 5) (by simp) with h728 | h728
                                                    · linarith only [h693, h728, hlam]
                                                    · linarith only [h651, h728, hlam]
                                                  · linarith only [h727, hlam, p696_0]
                                                · linarith only [h621, h726, hlam]
                                          · have p696_0 := h696c.1
                                            have p696_1 := h696c.2.1
                                            have p696_2 := h696c.2.2.1
                                            have p696_3 := h696c.2.2.2
                                            rcases p696_3 (m.d 0 2) (by simp) with h733 | h733
                                            · linarith only [h623, h733, hlam]
                                            · linarith only [h0, h733, hlam]
                                          · have p696_0 := h696c.1
                                            have p696_1 := h696c.2.1
                                            have p696_2 := h696c.2.2.1
                                            have p696_3 := h696c.2.2.2
                                            linarith only [h691, hlam, p696_1]
                                          · have p696_0 := h696c.1
                                            have p696_1 := h696c.2.1
                                            have p696_2 := h696c.2.2.1
                                            have p696_3 := h696c.2.2.2
                                            linarith only [hlam, p696_0]
                                          · have p696_0 := h696c.1
                                            have p696_1 := h696c.2.1
                                            have p696_2 := h696c.2.2.1
                                            have p696_3 := h696c.2.2.2
                                            linarith only [h619, h667, h683, h693, hc12, hc24, hlam, hphi, p696_1]
                                          · have p696_0 := h696c.1
                                            have p696_1 := h696c.2.1
                                            have p696_2 := h696c.2.2.1
                                            have p696_3 := h696c.2.2.2
                                            rcases p696_3 (m.d 0 2) (by simp) with h739 | h739
                                            · linarith only [h739, hlam, p696_0]
                                            · rcases p696_3 (m.d 1 2) (by simp) with h741 | h741
                                              · linarith only [h685, h741, hlam]
                                              · rcases p696_3 (m.d 2 3) (by simp) with h743 | h743
                                                · rcases p696_3 (m.d 2 4) (by simp) with h744 | h744
                                                  · rcases p696_3 (m.d 2 5) (by simp) with h745 | h745
                                                    · rcases h3bigk with h746c | h746c | h746c | h746c | h746c | h746c | h746c | h746c | h746c | h746c | h746c | h746c | h746c | h746c | h746c | h746c | h746c | h746c | h746c | h746c | h746c | h746c | h746c | h746c | h746c
                                                      · have p746_0 := h746c.1
                                                        have p746_1 := h746c.2.1
                                                        have p746_2 := h746c.2.2.1
                                                        have p746_3 := h746c.2.2.2
                                                        linarith only [hlam, p746_0]
                                                      · have p746_0 := h746c.1
                                                        have p746_1 := h746c.2.1
                                                        have p746_2 := h746c.2.2.1
                                                        have p746_3 := h746c.2.2.2
                                                        linarith only [h1, hlam, p746_1]
                                                      · have p746_0 := h746c.1
                                                        have p746_1 := h746c.2.1
                                                        have p746_2 := h746c.2.2.1
                                                        have p746_3 := h746c.2.2.2
                                                        linarith only [h621, hlam, p746_1]
                                                      · have p746_0 := h746c.1
                                                        have p746_1 := h746c.2.1
                                                        have p746_2 := h746c.2.2.1
                                                        have p746_3 := h746c.2.2.2
                                                        linarith only [hc34, hlam, hphi, ht0b, ht45, ht5b, p746_1, u0elo2]
                                                      · have p746_0 := h746c.1
                                                        have p746_1 := h746c.2.1
                                                        have p746_2 := h746c.2.2.1
                                                        have p746_3 := h746c.2.2.2
                                                        linarith only [hc35, hlam, hphi, ht0b, ht5b, p746_1, u0elo2]
                                                      · have p746_0 := h746c.1
                                                        have p746_1 := h746c.2.1
                                                        have p746_2 := h746c.2.2.1
                                                        have p746_3 := h746c.2.2.2
                                                        linarith only [h1, h620, h681, h683, h689, hc12, hc23, hlam, hphi, p746_1]
                                                      · have p746_0 := h746c.1
                                                        have p746_1 := h746c.2.1
                                                        have p746_2 := h746c.2.2.1
                                                        have p746_3 := h746c.2.2.2
                                                        linarith only [hlam, p746_0]
                                                      · have p746_0 := h746c.1
                                                        have p746_1 := h746c.2.1
                                                        have p746_2 := h746c.2.2.1
                                                        have p746_3 := h746c.2.2.2
                                                        linarith only [h681, hlam, p746_1]
                                                      · have p746_0 := h746c.1
                                                        have p746_1 := h746c.2.1
                                                        have p746_2 := h746c.2.2.1
                                                        have p746_3 := h746c.2.2.2
                                                        rcases p746_3 (m.d 0 3) (by simp) with h755 | h755
                                                        · linarith only [h1, h755, hlam]
                                                        · linarith only [h665, h755, hlam]
                                                      · have p746_0 := h746c.1
                                                        have p746_1 := h746c.2.1
                                                        have p746_2 := h746c.2.2.1
                                                        have p746_3 := h746c.2.2.2
                                                        rcases p746_3 (m.d 0 3) (by simp) with h758 | h758
                                                        · linarith only [h1, h758, hlam]
                                                        · linarith only [h666, h758, hlam]
                                                      · have p746_0 := h746c.1
                                                        have p746_1 := h746c.2.1
                                                        have p746_2 := h746c.2.2.1
                                                        have p746_3 := h746c.2.2.2
                                                        linarith only [h1, h620, h683, h689, hc12, hc23, hlam, hphi, p746_1]
                                                      · have p746_0 := h746c.1
                                                        have p746_1 := h746c.2.1
                                                        have p746_2 := h746c.2.2.1
                                                        have p746_3 := h746c.2.2.2
                                                        linarith only [h1, h620, h683, h689, hc12, hc23, hlam, hphi, p746_1]
                                                      · have p746_0 := h746c.1
                                                        have p746_1 := h746c.2.1
                                                        have p746_2 := h746c.2.2.1
                                                        have p746_3 := h746c.2.2.2
                                                        linarith only [hlam, p746_0]
                                                      · have p746_0 := h746c.1
                                                        have p746_1 := h746c.2.1
                                                        have p746_2 := h746c.2.2.1
                                                        have p746_3 := h746c.2.2.2
                                                        rcases p746_3 (m.d 0 3) (by simp) with h764 | h764
                                                        · linarith only [h621, h764, hlam]
                                                        · linarith only [h665, h764, hlam]
                                                      · have p746_0 := h746c.1
                                                        have p746_1 := h746c.2.1
                                                        have p746_2 := h746c.2.2.1
                                                        have p746_3 := h746c.2.2.2
                                                        rcases p746_3 (m.d 0 3) (by simp) with h767 | h767
                                                        · linarith only [h621, h767, hlam]
                                                        · linarith only [h666, h767, hlam]
                                                      · have p746_0 := h746c.1
                                                        have p746_1 := h746c.2.1
                                                        have p746_2 := h746c.2.2.1
                                                        have p746_3 := h746c.2.2.2
                                                        linarith only [h665, hlam, p746_0]
                                                      · have p746_0 := h746c.1
                                                        have p746_1 := h746c.2.1
                                                        have p746_2 := h746c.2.2.1
                                                        have p746_3 := h746c.2.2.2
                                                        linarith only [h687, hlam, p746_0]
                                                      · have p746_0 := h746c.1
                                                        have p746_1 := h746c.2.1
                                                        have p746_2 := h746c.2.2.1
                                                        have p746_3 := h746c.2.2.2
                                                        linarith only [h691, hlam, p746_0]
                                                      · have p746_0 := h746c.1
                                                        have p746_1 := h746c.2.1
                                                        have p746_2 := h746c.2.2.1
                                                        have p746_3 := h746c.2.2.2
                                                        linarith only [hlam, p746_0]
                                                      · have p746_0 := h746c.1
                                                        have p746_1 := h746c.2.1
                                                        have p746_2 := h746c.2.2.1
                                                        have p746_3 := h746c.2.2.2
                                                        linarith only [h694, hlam, p746_1]
                                                      · have p746_0 := h746c.1
                                                        have p746_1 := h746c.2.1
                                                        have p746_2 := h746c.2.2.1
                                                        have p746_3 := h746c.2.2.2
                                                        linarith only [h666, hlam, p746_0]
                                                      · have p746_0 := h746c.1
                                                        have p746_1 := h746c.2.1
                                                        have p746_2 := h746c.2.2.1
                                                        have p746_3 := h746c.2.2.2
                                                        linarith only [h688, hlam, p746_0]
                                                      · have p746_0 := h746c.1
                                                        have p746_1 := h746c.2.1
                                                        have p746_2 := h746c.2.2.1
                                                        have p746_3 := h746c.2.2.2
                                                        linarith only [h692, hlam, p746_0]
                                                      · have p746_0 := h746c.1
                                                        have p746_1 := h746c.2.1
                                                        have p746_2 := h746c.2.2.1
                                                        have p746_3 := h746c.2.2.2
                                                        linarith only [h666, hc34, hlam, hphi, ht0b, ht45, ht5b, p746_1, u0elo2]
                                                      · have p746_0 := h746c.1
                                                        have p746_1 := h746c.2.1
                                                        have p746_2 := h746c.2.2.1
                                                        have p746_3 := h746c.2.2.2
                                                        linarith only [hlam, p746_0]
                                                    · linarith only [h745, hlam, p696_0]
                                                  · linarith only [h623, h744, hlam]
                                                · linarith only [h621, h743, hlam]
                                          · have p696_0 := h696c.1
                                            have p696_1 := h696c.2.1
                                            have p696_2 := h696c.2.2.1
                                            have p696_3 := h696c.2.2.2
                                            rcases p696_3 (m.d 0 2) (by simp) with h783 | h783
                                            · linarith only [h651, h783, hlam]
                                            · linarith only [h0, h783, hlam]
                                          · have p696_0 := h696c.1
                                            have p696_1 := h696c.2.1
                                            have p696_2 := h696c.2.2.1
                                            have p696_3 := h696c.2.2.2
                                            linarith only [h692, hlam, p696_1]
                                          · have p696_0 := h696c.1
                                            have p696_1 := h696c.2.1
                                            have p696_2 := h696c.2.2.1
                                            have p696_3 := h696c.2.2.2
                                            linarith only [h693, hlam, p696_0]
                                          · have p696_0 := h696c.1
                                            have p696_1 := h696c.2.1
                                            have p696_2 := h696c.2.2.1
                                            have p696_3 := h696c.2.2.2
                                            linarith only [hlam, p696_0]
                                      · rcases m.htr 3 4 5 (by decide) (by decide) with h789 | h789
                                        · linarith only [h0, h623, h693, h789, hc12, hc34, hlam, hphi, ht23]
                                        · rcases h2bigk with h791c | h791c | h791c | h791c | h791c | h791c | h791c | h791c | h791c | h791c | h791c | h791c | h791c | h791c | h791c | h791c | h791c | h791c | h791c | h791c | h791c | h791c | h791c | h791c | h791c
                                          · have p791_0 := h791c.1
                                            have p791_1 := h791c.2.1
                                            have p791_2 := h791c.2.2.1
                                            have p791_3 := h791c.2.2.2
                                            linarith only [hlam, p791_0]
                                          · have p791_0 := h791c.1
                                            have p791_1 := h791c.2.1
                                            have p791_2 := h791c.2.2.1
                                            have p791_3 := h791c.2.2.2
                                            linarith only [hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p791_1, u0elo1]
                                          · have p791_0 := h791c.1
                                            have p791_1 := h791c.2.1
                                            have p791_2 := h791c.2.2.1
                                            have p791_3 := h791c.2.2.2
                                            linarith only [h621, hlam, p791_0]
                                          · have p791_0 := h791c.1
                                            have p791_1 := h791c.2.1
                                            have p791_2 := h791c.2.2.1
                                            have p791_3 := h791c.2.2.2
                                            linarith only [h623, hlam, p791_0]
                                          · have p791_0 := h791c.1
                                            have p791_1 := h791c.2.1
                                            have p791_2 := h791c.2.2.1
                                            have p791_3 := h791c.2.2.2
                                            linarith only [h651, hlam, p791_0]
                                          · have p791_0 := h791c.1
                                            have p791_1 := h791c.2.1
                                            have p791_2 := h791c.2.2.1
                                            have p791_3 := h791c.2.2.2
                                            linarith only [h0, hlam, p791_0]
                                          · have p791_0 := h791c.1
                                            have p791_1 := h791c.2.1
                                            have p791_2 := h791c.2.2.1
                                            have p791_3 := h791c.2.2.2
                                            linarith only [hlam, p791_0]
                                          · have p791_0 := h791c.1
                                            have p791_1 := h791c.2.1
                                            have p791_2 := h791c.2.2.1
                                            have p791_3 := h791c.2.2.2
                                            linarith only [h681, hlam, p791_0]
                                          · have p791_0 := h791c.1
                                            have p791_1 := h791c.2.1
                                            have p791_2 := h791c.2.2.1
                                            have p791_3 := h791c.2.2.2
                                            linarith only [h683, hlam, p791_0]
                                          · have p791_0 := h791c.1
                                            have p791_1 := h791c.2.1
                                            have p791_2 := h791c.2.2.1
                                            have p791_3 := h791c.2.2.2
                                            linarith only [h685, hlam, p791_0]
                                          · have p791_0 := h791c.1
                                            have p791_1 := h791c.2.1
                                            have p791_2 := h791c.2.2.1
                                            have p791_3 := h791c.2.2.2
                                            rcases p791_3 (m.d 0 2) (by simp) with h802 | h802
                                            · linarith only [h802, hlam, p791_0]
                                            · rcases p791_3 (m.d 1 2) (by simp) with h804 | h804
                                              · linarith only [h681, h804, hlam]
                                              · rcases p791_3 (m.d 2 3) (by simp) with h806 | h806
                                                · rcases p791_3 (m.d 2 4) (by simp) with h807 | h807
                                                  · linarith only [h691, h807, hlam]
                                                  · linarith only [h623, h807, hlam]
                                                · linarith only [h806, hlam, p791_0]
                                          · have p791_0 := h791c.1
                                            have p791_1 := h791c.2.1
                                            have p791_2 := h791c.2.2.1
                                            have p791_3 := h791c.2.2.2
                                            rcases p791_3 (m.d 0 2) (by simp) with h811 | h811
                                            · linarith only [h621, h811, hlam]
                                            · linarith only [h0, h811, hlam]
                                          · have p791_0 := h791c.1
                                            have p791_1 := h791c.2.1
                                            have p791_2 := h791c.2.2.1
                                            have p791_3 := h791c.2.2.2
                                            linarith only [hlam, p791_0]
                                          · have p791_0 := h791c.1
                                            have p791_1 := h791c.2.1
                                            have p791_2 := h791c.2.2.1
                                            have p791_3 := h791c.2.2.2
                                            linarith only [h623, hc02, hc23, hlam, hphi, p791_1]
                                          · have p791_0 := h791c.1
                                            have p791_1 := h791c.2.1
                                            have p791_2 := h791c.2.2.1
                                            have p791_3 := h791c.2.2.2
                                            linarith only [h0, h651, hc12, hc23, hlam, hphi, p791_1]
                                          · have p791_0 := h791c.1
                                            have p791_1 := h791c.2.1
                                            have p791_2 := h791c.2.2.1
                                            have p791_3 := h791c.2.2.2
                                            linarith only [h0, h693, hc12, hc45, hlam, hphi, ht23, ht34, p791_1]
                                          · have p791_0 := h791c.1
                                            have p791_1 := h791c.2.1
                                            have p791_2 := h791c.2.2.1
                                            have p791_3 := h791c.2.2.2
                                            linarith only [h693, hc12, hc45, hlam, hphi, ht23, ht34, p791_1]
                                          · have p791_0 := h791c.1
                                            have p791_1 := h791c.2.1
                                            have p791_2 := h791c.2.2.1
                                            have p791_3 := h791c.2.2.2
                                            linarith only [h691, hlam, p791_1]
                                          · have p791_0 := h791c.1
                                            have p791_1 := h791c.2.1
                                            have p791_2 := h791c.2.2.1
                                            have p791_3 := h791c.2.2.2
                                            linarith only [hlam, p791_0]
                                          · have p791_0 := h791c.1
                                            have p791_1 := h791c.2.1
                                            have p791_2 := h791c.2.2.1
                                            have p791_3 := h791c.2.2.2
                                            linarith only [h693, hlam, p791_1]
                                          · have p791_0 := h791c.1
                                            have p791_1 := h791c.2.1
                                            have p791_2 := h791c.2.2.1
                                            have p791_3 := h791c.2.2.2
                                            rcases p791_3 (m.d 0 2) (by simp) with h822 | h822
                                            · linarith only [h822, hlam, p791_0]
                                            · rcases p791_3 (m.d 1 2) (by simp) with h824 | h824
                                              · linarith only [h685, h824, hlam]
                                              · rcases p791_3 (m.d 2 3) (by simp) with h826 | h826
                                                · rcases p791_3 (m.d 2 4) (by simp) with h827 | h827
                                                  · linarith only [h693, h827, hlam]
                                                  · linarith only [h623, h827, hlam]
                                                · linarith only [h621, h826, hlam]
                                          · have p791_0 := h791c.1
                                            have p791_1 := h791c.2.1
                                            have p791_2 := h791c.2.2.1
                                            have p791_3 := h791c.2.2.2
                                            rcases p791_3 (m.d 0 2) (by simp) with h831 | h831
                                            · linarith only [h651, h831, hlam]
                                            · linarith only [h0, h831, hlam]
                                          · have p791_0 := h791c.1
                                            have p791_1 := h791c.2.1
                                            have p791_2 := h791c.2.2.1
                                            have p791_3 := h791c.2.2.2
                                            linarith only [h692, hlam, p791_1]
                                          · have p791_0 := h791c.1
                                            have p791_1 := h791c.2.1
                                            have p791_2 := h791c.2.2.1
                                            have p791_3 := h791c.2.2.2
                                            linarith only [h0, h623, hc12, hc25, hlam, hphi, p791_1]
                                          · have p791_0 := h791c.1
                                            have p791_1 := h791c.2.1
                                            have p791_2 := h791c.2.2.1
                                            have p791_3 := h791c.2.2.2
                                            linarith only [hlam, p791_0]
                                    · linarith only [h620, h688, h692, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                                  · linarith only [h1, h620, h681, h687, h689, h691, hlam]
                              · linarith only [h0, h1, h688, hc12, hc35, hlam, hphi, ht23]
                            · linarith only [h0, h1, h687, hc12, hc34, hlam, hphi, ht23]
                  · linarith only [h1, h620, h666, hlam]
                · linarith only [h1, h619, h665, hlam]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h843 | h843
          · linarith only [h0, h1, h843, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h845 | h845
            · rcases m.htr 0 2 5 (by decide) (by decide) with h846 | h846
              · linarith only [h0, h620, h846, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h848 | h848
                · rcases m.htr 0 3 5 (by decide) (by decide) with h849 | h849
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h850 | h850
                    · linarith only [h0, h620, h845, h850, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h852 | h852
                      · linarith only [h0, h843, h852, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h854 | h854
                        · linarith only [h0, h620, h849, h854, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                        · linarith only [h845, h854, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h857 | h857
                    · linarith only [h0, h1, h845, h849, h857, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h859 | h859
                      · linarith only [h0, h1, h843, h849, h859, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo4]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h861 | h861
                        · linarith only [h0, h1, h849, h861, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo4]
                        · linarith only [h845, h861, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                · linarith only [h1, h619, h848, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h865 | h865
              · linarith only [h619, h620, h845, h865, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h867 | h867
                · rcases m.htr 0 3 5 (by decide) (by decide) with h868 | h868
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h869 | h869
                    · linarith only [h619, h620, h869, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h871 | h871
                      · linarith only [h0, h620, h843, h868, h871, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h873 | h873
                        · linarith only [h0, h620, h845, h868, h873, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h875 | h875
                          · linarith only [h619, h620, h865, h868, h873, h875, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h877 | h877
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h878 | h878
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h879 | h879
                                · linarith only [h619, h620, h868, h869, h879, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h881 | h881
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h882 | h882
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h883 | h883
                                      · linarith only [h0, h620, h879, h883, hc12, hc24, hlam, hphi]
                                      · rcases m.htr 3 4 5 (by decide) (by decide) with h885 | h885
                                        · linarith only [h0, h845, h883, h885, hc12, hc34, hlam, hphi, ht23]
                                        · rcases h2bigk with h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c | h887c
                                          · have p887_0 := h887c.1
                                            have p887_1 := h887c.2.1
                                            have p887_2 := h887c.2.2.1
                                            have p887_3 := h887c.2.2.2
                                            linarith only [hlam, p887_0]
                                          · have p887_0 := h887c.1
                                            have p887_1 := h887c.2.1
                                            have p887_2 := h887c.2.2.1
                                            have p887_3 := h887c.2.2.2
                                            linarith only [hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p887_1, u0elo1]
                                          · have p887_0 := h887c.1
                                            have p887_1 := h887c.2.1
                                            have p887_2 := h887c.2.2.1
                                            have p887_3 := h887c.2.2.2
                                            linarith only [h843, hlam, p887_0]
                                          · have p887_0 := h887c.1
                                            have p887_1 := h887c.2.1
                                            have p887_2 := h887c.2.2.1
                                            have p887_3 := h887c.2.2.2
                                            linarith only [h845, hlam, p887_0]
                                          · have p887_0 := h887c.1
                                            have p887_1 := h887c.2.1
                                            have p887_2 := h887c.2.2.1
                                            have p887_3 := h887c.2.2.2
                                            linarith only [h865, hlam, p887_0]
                                          · have p887_0 := h887c.1
                                            have p887_1 := h887c.2.1
                                            have p887_2 := h887c.2.2.1
                                            have p887_3 := h887c.2.2.2
                                            linarith only [h0, hlam, p887_0]
                                          · have p887_0 := h887c.1
                                            have p887_1 := h887c.2.1
                                            have p887_2 := h887c.2.2.1
                                            have p887_3 := h887c.2.2.2
                                            linarith only [hlam, p887_0]
                                          · have p887_0 := h887c.1
                                            have p887_1 := h887c.2.1
                                            have p887_2 := h887c.2.2.1
                                            have p887_3 := h887c.2.2.2
                                            linarith only [h871, hlam, p887_0]
                                          · have p887_0 := h887c.1
                                            have p887_1 := h887c.2.1
                                            have p887_2 := h887c.2.2.1
                                            have p887_3 := h887c.2.2.2
                                            linarith only [h873, hlam, p887_0]
                                          · have p887_0 := h887c.1
                                            have p887_1 := h887c.2.1
                                            have p887_2 := h887c.2.2.1
                                            have p887_3 := h887c.2.2.2
                                            linarith only [h875, hlam, p887_0]
                                          · have p887_0 := h887c.1
                                            have p887_1 := h887c.2.1
                                            have p887_2 := h887c.2.2.1
                                            have p887_3 := h887c.2.2.2
                                            rcases p887_3 (m.d 0 2) (by simp) with h898 | h898
                                            · linarith only [h898, hlam, p887_0]
                                            · rcases p887_3 (m.d 1 2) (by simp) with h900 | h900
                                              · linarith only [h871, h900, hlam]
                                              · rcases p887_3 (m.d 2 3) (by simp) with h902 | h902
                                                · rcases p887_3 (m.d 2 4) (by simp) with h903 | h903
                                                  · linarith only [h881, h903, hlam]
                                                  · linarith only [h845, h903, hlam]
                                                · linarith only [h902, hlam, p887_0]
                                          · have p887_0 := h887c.1
                                            have p887_1 := h887c.2.1
                                            have p887_2 := h887c.2.2.1
                                            have p887_3 := h887c.2.2.2
                                            rcases p887_3 (m.d 0 2) (by simp) with h907 | h907
                                            · linarith only [h843, h907, hlam]
                                            · linarith only [h0, h907, hlam]
                                          · have p887_0 := h887c.1
                                            have p887_1 := h887c.2.1
                                            have p887_2 := h887c.2.2.1
                                            have p887_3 := h887c.2.2.2
                                            linarith only [hlam, p887_0]
                                          · have p887_0 := h887c.1
                                            have p887_1 := h887c.2.1
                                            have p887_2 := h887c.2.2.1
                                            have p887_3 := h887c.2.2.2
                                            linarith only [h845, hc02, hc23, hlam, hphi, p887_1]
                                          · have p887_0 := h887c.1
                                            have p887_1 := h887c.2.1
                                            have p887_2 := h887c.2.2.1
                                            have p887_3 := h887c.2.2.2
                                            linarith only [h619, h620, h873, h875, hc12, hc23, hlam, hphi, p887_1]
                                          · have p887_0 := h887c.1
                                            have p887_1 := h887c.2.1
                                            have p887_2 := h887c.2.2.1
                                            have p887_3 := h887c.2.2.2
                                            linarith only [h0, h883, hc12, hc45, hlam, hphi, ht23, ht34, p887_1]
                                          · have p887_0 := h887c.1
                                            have p887_1 := h887c.2.1
                                            have p887_2 := h887c.2.2.1
                                            have p887_3 := h887c.2.2.2
                                            linarith only [h883, hc12, hc45, hlam, hphi, ht23, ht34, p887_1]
                                          · have p887_0 := h887c.1
                                            have p887_1 := h887c.2.1
                                            have p887_2 := h887c.2.2.1
                                            have p887_3 := h887c.2.2.2
                                            linarith only [h881, hlam, p887_1]
                                          · have p887_0 := h887c.1
                                            have p887_1 := h887c.2.1
                                            have p887_2 := h887c.2.2.1
                                            have p887_3 := h887c.2.2.2
                                            linarith only [hlam, p887_0]
                                          · have p887_0 := h887c.1
                                            have p887_1 := h887c.2.1
                                            have p887_2 := h887c.2.2.1
                                            have p887_3 := h887c.2.2.2
                                            linarith only [h883, hlam, p887_1]
                                          · have p887_0 := h887c.1
                                            have p887_1 := h887c.2.1
                                            have p887_2 := h887c.2.2.1
                                            have p887_3 := h887c.2.2.2
                                            rcases p887_3 (m.d 0 2) (by simp) with h918 | h918
                                            · linarith only [h918, hlam, p887_0]
                                            · rcases p887_3 (m.d 1 2) (by simp) with h920 | h920
                                              · linarith only [h875, h920, hlam]
                                              · rcases p887_3 (m.d 2 3) (by simp) with h922 | h922
                                                · rcases p887_3 (m.d 2 4) (by simp) with h923 | h923
                                                  · linarith only [h883, h923, hlam]
                                                  · linarith only [h845, h923, hlam]
                                                · linarith only [h843, h922, hlam]
                                          · have p887_0 := h887c.1
                                            have p887_1 := h887c.2.1
                                            have p887_2 := h887c.2.2.1
                                            have p887_3 := h887c.2.2.2
                                            rcases p887_3 (m.d 0 2) (by simp) with h927 | h927
                                            · linarith only [h865, h927, hlam]
                                            · linarith only [h0, h927, hlam]
                                          · have p887_0 := h887c.1
                                            have p887_1 := h887c.2.1
                                            have p887_2 := h887c.2.2.1
                                            have p887_3 := h887c.2.2.2
                                            linarith only [h882, hlam, p887_1]
                                          · have p887_0 := h887c.1
                                            have p887_1 := h887c.2.1
                                            have p887_2 := h887c.2.2.1
                                            have p887_3 := h887c.2.2.2
                                            linarith only [h0, h845, hc12, hc25, hlam, hphi, p887_1]
                                          · have p887_0 := h887c.1
                                            have p887_1 := h887c.2.1
                                            have p887_2 := h887c.2.2.1
                                            have p887_3 := h887c.2.2.2
                                            linarith only [hlam, p887_0]
                                    · linarith only [h868, h882, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                                  · linarith only [h619, h620, h871, h877, h878, h881, hlam]
                              · linarith only [h868, h878, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                            · linarith only [h1, h619, h873, h877, hc12, hc34, hlam, hphi, ht23]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h937 | h937
                    · linarith only [h1, h619, h868, h937, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h939 | h939
                      · linarith only [h0, h939, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h941 | h941
                        · linarith only [h0, h845, h941, hlam]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h943 | h943
                          · linarith only [h619, h941, h943, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h945 | h945
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h946 | h946
                              · linarith only [h1, h619, h868, h939, h941, h946, hc12, hc23, hlam, hphi]
                              · linarith only [h1, h619, h941, h946, hc12, hc35, hlam, hphi, ht23]
                            · linarith only [h1, h619, h941, h945, hc12, hc34, hlam, hphi, ht23]
                · linarith only [h1, h619, h867, hlam]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h951 | h951
        · rcases m.htr 0 2 3 (by decide) (by decide) with h952 | h952
          · linarith only [h0, h1, h952, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h954 | h954
            · linarith only [h0, h619, h954, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h956 | h956
              · rcases m.htr 0 3 4 (by decide) (by decide) with h957 | h957
                · rcases m.htr 0 3 5 (by decide) (by decide) with h958 | h958
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h959 | h959
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h960 | h960
                      · linarith only [h0, h960, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h962 | h962
                        · linarith only [h0, h619, h954, h957, h962, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h964 | h964
                          · linarith only [h0, h619, h957, h964, hc25, hlam, hphi, ht0b, ht5b, u0elo2]
                          · linarith only [h956, h964, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h0, h619, h956, h959, hlam]
                  · linarith only [h0, h619, h956, h957, h958, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h969 | h969
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h970 | h970
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h971 | h971
                      · linarith only [h0, h952, h971, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h973 | h973
                        · linarith only [h0, h1, h954, h956, h957, h973, hc25, hlam, hphi, ht0b, ht5b, u0elo3]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h975 | h975
                          · linarith only [h0, h1, h957, h975, hc25, hlam, hphi, ht0b, ht5b, u0elo3]
                          · linarith only [h956, h975, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                    · linarith only [h0, h1, h956, h957, h970, hlam]
                  · linarith only [h0, h1, h956, h969, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h980 | h980
                · rcases m.htr 0 3 5 (by decide) (by decide) with h981 | h981
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h982 | h982
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h983 | h983
                      · linarith only [h0, h952, h983, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h985 | h985
                        · linarith only [h0, h619, h951, h954, h985, hc15, hlam, hphi, ht0b, ht5b, u0elo1]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h987 | h987
                          · linarith only [h0, h956, h987, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h989 | h989
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h990 | h990
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h991 | h991
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h992 | h992
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h993 | h993
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h994 | h994
                                      · rcases m.htr 3 4 5 (by decide) (by decide) with h995 | h995
                                        · linarith only [h980, h995, hc45, hlam, hphi, ht0b, ht5b, u0elo2]
                                        · linarith only [h980, h982, h995, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                                      · linarith only [h0, h619, h985, h994, hc12, hc45, hlam, hphi, ht23, ht34]
                                    · linarith only [h619, h951, h983, h989, h990, h993, hlam]
                                  · linarith only [h619, h951, h983, h987, h989, h992, hc12, hc34, hlam, hphi, ht23]
                                · linarith only [h619, h951, h987, h991, hc12, hc45, hlam, hphi, ht23, ht34]
                              · linarith only [h619, h951, h987, h989, h990, hc12, hc35, hlam, hphi, ht23]
                            · linarith only [h980, h989, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                    · linarith only [h619, h951, h982, hlam]
                  · linarith only [h619, h951, h980, h981, hlam]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h1006 | h1006
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1007 | h1007
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1008 | h1008
                      · linarith only [h0, h1006, h1008, h952, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h1010 | h1010
                        · linarith only [h0, h1, h1010, h980, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h1012 | h1012
                          · linarith only [h0, h1, h1012, h980, hc25, hlam, hphi, ht0b, ht5b, u0elo3]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h1014 | h1014
                            · linarith only [h1, h1008, h1012, h1014, h951, h980, hc12, hc23, hlam, hphi]
                            · linarith only [h1, h1012, h1014, h951, hc12, hc34, hlam, hphi, ht23]
                    · linarith only [h1, h1007, h951, h980, hlam]
                  · linarith only [h1, h1006, h951, hlam]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h1019 | h1019
          · linarith only [h0, h1, h1019, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h1021 | h1021
            · linarith only [h0, h1021, h619, hlam]
            · rcases m.htr 0 2 5 (by decide) (by decide) with h1023 | h1023
              · linarith only [h0, h1023, h951, hlam]
              · rcases m.htr 0 3 4 (by decide) (by decide) with h1025 | h1025
                · rcases m.htr 0 3 5 (by decide) (by decide) with h1026 | h1026
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1027 | h1027
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1028 | h1028
                      · linarith only [h0, h1019, h1025, h1027, h1028, h951, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h1030 | h1030
                        · linarith only [h0, h1021, h1027, h1030, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h1032 | h1032
                          · linarith only [h0, h1023, h1032, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h1034 | h1034
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h1035 | h1035
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h1036 | h1036
                                · rcases m.htr 2 3 4 (by decide) (by decide) with h1037 | h1037
                                  · rcases m.htr 2 3 5 (by decide) (by decide) with h1038 | h1038
                                    · rcases m.htr 2 4 5 (by decide) (by decide) with h1039 | h1039
                                      · rcases m.htr 3 4 5 (by decide) (by decide) with h1040 | h1040
                                        · linarith only [h1025, h1040, hc45, hlam, hphi, ht0b, ht5b, u0elo2]
                                        · linarith only [h1025, h1027, h1040, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                                      · linarith only [h1025, h1027, h1030, h1036, h1039, h951, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                                    · linarith only [h0, h1026, h1028, h1034, h1036, h1038, h951, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                                  · linarith only [h0, h1028, h1034, h1036, h1037, h951, hc12, hc34, hlam, hphi, ht23]
                                · linarith only [h1025, h1027, h1036, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                              · linarith only [h0, h1026, h1034, h1035, h619, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                            · linarith only [h1025, h1034, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1049 | h1049
                      · linarith only [h0, h1019, h1049, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h1051 | h1051
                        · linarith only [h0, h1026, h1027, h1051, h619, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h1053 | h1053
                          · linarith only [h0, h1026, h1027, h1053, h619, hc25, hlam, hphi, ht0b, ht5b, u0elo2]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h1055 | h1055
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h1056 | h1056
                              · rcases m.htr 1 4 5 (by decide) (by decide) with h1057 | h1057
                                · linarith only [h0, h1027, h1049, h1055, h1057, h619, hc12, hc23, hlam, hphi]
                                · linarith only [h0, h1057, h619, hc12, hc45, hlam, hphi, ht23, ht34]
                              · linarith only [h1026, h1056, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                            · linarith only [h0, h1, h1055, hc12, hc34, hlam, hphi, ht23]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1062 | h1062
                    · linarith only [h1025, h1026, h1062, hlam]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1064 | h1064
                      · linarith only [h0, h1064, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h1066 | h1066
                        · linarith only [h0, h1025, h1026, h1066, h619, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo4]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h1068 | h1068
                          · linarith only [h0, h1025, h1026, h1068, h619, hc25, hlam, hphi, ht0b, ht5b, u0elo4]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h1070 | h1070
                            · rcases m.htr 1 3 5 (by decide) (by decide) with h1071 | h1071
                              · linarith only [h0, h1025, h1026, h1064, h1071, h619, hc12, hc23, hlam, hphi]
                              · linarith only [h0, h1, h1071, hc12, hc35, hlam, hphi, ht23]
                            · linarith only [h0, h1, h1025, h1026, h1070, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo4]
                · rcases m.htr 0 3 5 (by decide) (by decide) with h1075 | h1075
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1076 | h1076
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1077 | h1077
                      · linarith only [h0, h1077, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h1079 | h1079
                        · linarith only [h0, h1021, h1025, h1075, h1079, h951, hlam]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h1081 | h1081
                          · linarith only [h0, h1023, h1081, h951, hlam]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h1083 | h1083
                            · linarith only [h0, h1025, h1075, h1077, h1083, h951, hc12, hc23, hlam, hphi]
                            · linarith only [h0, h1, h1083, hc12, hc34, hlam, hphi, ht23]
                    · linarith only [h1025, h1075, h1076, hlam]
                  · rcases m.htr 0 4 5 (by decide) (by decide) with h1087 | h1087
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1088 | h1088
                      · linarith only [h0, h1088, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h1090 | h1090
                        · linarith only [h0, h1, h1075, h1087, h1090, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h1092 | h1092
                          · linarith only [h0, h1, h1075, h1087, h1092, hc25, hlam, hphi, ht0b, ht5b, u0elo3]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h1094 | h1094
                            · linarith only [h0, h1, h1025, h1088, h1094, hc12, hc23, hlam, hphi]
                            · linarith only [h0, h1, h1094, hc12, hc34, hlam, hphi, ht23]
                    · rcases m.htr 1 2 3 (by decide) (by decide) with h1097 | h1097
                      · linarith only [h0, h1097, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 2 4 (by decide) (by decide) with h1099 | h1099
                        · linarith only [h0, h1, h1025, h1087, h1099, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo4]
                        · rcases m.htr 1 2 5 (by decide) (by decide) with h1101 | h1101
                          · linarith only [h0, h1, h1025, h1087, h1101, hc25, hlam, hphi, ht0b, ht5b, u0elo4]
                          · rcases m.htr 1 3 4 (by decide) (by decide) with h1103 | h1103
                            · linarith only [h0, h1, h1025, h1097, h1103, hc12, hc23, hlam, hphi]
                            · linarith only [h0, h1, h1103, hc12, hc34, hlam, hphi, ht23]
  · exact r1l7_20_12_13_15_H_L_L_I_L_I_L_I_s0 m hb0 hb2 hb3 hb5 h0

end R2N4
