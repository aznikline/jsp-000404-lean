import Jsp000404.S7N7Defs
import Jsp000404.R1LeavesN7_35S4

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 8226000 in
set_option maxHeartbeats 8226000 in
theorem r1l7_20_11_13_14_H_L_L_I_L_I_L_I (m : N7Model)
    (hb0 : CMSig2_7_H_L m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb1 : CMSig1_7_L_I m.lam m.p (m.t 1) (m.d 0 1) (m.d 1 2) (m.d 1 3) (m.d 1 4) (m.d 1 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb4 : CMSig1_7_L_I m.lam m.p (m.t 4) (m.d 0 4) (m.d 1 4) (m.d 2 4) (m.d 3 4) (m.d 4 5))
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
  have h1bigk := hb1.1
  have h3bigk := hb3.1
  have h4bigk := hb4.1
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
            · rcases m.htr 0 3 4 (by decide) (by decide) with h6 | h6
              · rcases m.htr 0 3 5 (by decide) (by decide) with h7 | h7
                · rcases m.htr 0 4 5 (by decide) (by decide) with h8 | h8
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h9 | h9
                    · linarith only [h0, h9, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · linarith only [h0, h4, h9, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h12 | h12
                    · linarith only [h0, h12, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · linarith only [h0, h12, h4, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h15 | h15
                  · linarith only [h15, h6, h7, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h17 | h17
                    · linarith only [h0, h17, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · linarith only [h0, h17, h4, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h20 | h20
                · rcases m.htr 0 4 5 (by decide) (by decide) with h21 | h21
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h22 | h22
                    · linarith only [h0, h22, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · linarith only [h0, h22, h4, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · linarith only [h20, h21, h6, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h26 | h26
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h27 | h27
                    · linarith only [h0, h27, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · linarith only [h0, h27, h4, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h30 | h30
                    · linarith only [h0, h30, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · linarith only [h0, h30, h4, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h33 | h33
              · linarith only [h33, h4, h5, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h35 | h35
                · rcases m.htr 0 4 5 (by decide) (by decide) with h36 | h36
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h37 | h37
                    · linarith only [h0, h37, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · linarith only [h37, h4, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                  · linarith only [h35, h36, h4, h5, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h41 | h41
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h42 | h42
                    · linarith only [h0, h42, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · linarith only [h2, h4, h42, h5, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h45 | h45
                    · linarith only [h0, h45, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · linarith only [h3, h4, h41, h45, h5, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h48 | h48
            · rcases m.htr 0 3 4 (by decide) (by decide) with h49 | h49
              · rcases m.htr 0 3 5 (by decide) (by decide) with h50 | h50
                · rcases m.htr 0 4 5 (by decide) (by decide) with h51 | h51
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h52 | h52
                    · linarith only [h0, h4, h52, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h54 | h54
                      · linarith only [h1, h52, h54, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · linarith only [h48, h54, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h57 | h57
                    · linarith only [h0, h4, h57, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h59 | h59
                      · linarith only [h1, h57, h59, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · linarith only [h48, h59, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h62 | h62
                  · linarith only [h4, h48, h50, h62, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h64 | h64
                    · linarith only [h0, h4, h48, h64, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h66 | h66
                      · linarith only [h1, h64, h66, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · linarith only [h48, h66, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
              · linarith only [h4, h48, h49, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h70 | h70
              · rcases m.htr 0 3 5 (by decide) (by decide) with h71 | h71
                · rcases m.htr 0 4 5 (by decide) (by decide) with h72 | h72
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h73 | h73
                    · linarith only [h0, h73, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h75 | h75
                      · linarith only [h1, h48, h73, h75, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h77 | h77
                        · linarith only [h0, h77, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h79 | h79
                          · linarith only [h1, h79, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                          · linarith only [h1, h70, h73, h79, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h82 | h82
                    · linarith only [h0, h4, h70, h82, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo1]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h84 | h84
                      · linarith only [h0, h48, h84, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h86 | h86
                        · linarith only [h0, h86, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h88 | h88
                          · linarith only [h1, h88, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                          · linarith only [h70, h82, h88, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h91 | h91
                  · linarith only [h70, h71, h91, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h93 | h93
                    · linarith only [h0, h4, h93, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h95 | h95
                      · linarith only [h0, h48, h95, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h97 | h97
                        · linarith only [h1, h93, h97, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h99 | h99
                          · linarith only [h1, h99, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                          · linarith only [h3, h70, h71, h93, h99, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h102 | h102
                · rcases m.htr 0 4 5 (by decide) (by decide) with h103 | h103
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h104 | h104
                    · linarith only [h0, h104, h4, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h106 | h106
                      · linarith only [h0, h102, h106, h48, h70, hc35, hlam, hphi, ht0b, ht5b, u0elo1]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h108 | h108
                        · linarith only [h1, h104, h108, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h110 | h110
                          · linarith only [h1, h102, h110, h70, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h112 | h112
                            · linarith only [h110, h112, h2, hc35, hlam, hphi, ht0b, ht5b, u0elo0]
                            · linarith only [h102, h104, h112, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                  · linarith only [h102, h103, h70, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h116 | h116
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h117 | h117
                    · linarith only [h0, h117, h4, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h119 | h119
                      · linarith only [h0, h119, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h121 | h121
                        · linarith only [h1, h117, h121, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h123 | h123
                          · linarith only [h1, h123, h4, h70, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h125 | h125
                            · linarith only [h1, h102, h125, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h127 | h127
                              · linarith only [h127, h2, hc45, hlam, hphi, ht0b, ht5b, u0elo0]
                              · linarith only [h116, h127, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h130 | h130
                    · linarith only [h0, h130, h4, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h132 | h132
                      · linarith only [h0, h132, h48, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h134 | h134
                        · linarith only [h0, h134, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h136 | h136
                          · linarith only [h1, h136, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h138 | h138
                            · linarith only [h1, h102, h138, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h140 | h140
                              · linarith only [h116, h140, h2, hlam]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h142 | h142
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h143 | h143
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h144 | h144
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h145 | h145
                                      · linarith only [h116, h142, h145, h4, h70, hc02, hc23, hlam, hphi]
                                      · linarith only [h0, h144, h145, h4, h70, hc12, hc24, hlam, hphi]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h148 | h148
                                      · linarith only [h0, h144, h148, h48, hc12, hc34, hlam, hphi, ht23]
                                      · rcases h1bigk with h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c
                                        · have p150_0 := h150c.1
                                          have p150_1 := h150c.2.1
                                          have p150_2 := h150c.2.2.1
                                          have p150_3 := h150c.2.2.2
                                          linarith only [hlam, p150_0]
                                        · have p150_0 := h150c.1
                                          have p150_1 := h150c.2.1
                                          have p150_2 := h150c.2.2.1
                                          have p150_3 := h150c.2.2.2
                                          linarith only [hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p150_1, u0elo0]
                                        · have p150_0 := h150c.1
                                          have p150_1 := h150c.2.1
                                          have p150_2 := h150c.2.2.1
                                          have p150_3 := h150c.2.2.2
                                          linarith only [hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p150_1, u0elo0]
                                        · have p150_0 := h150c.1
                                          have p150_1 := h150c.2.1
                                          have p150_2 := h150c.2.2.1
                                          have p150_3 := h150c.2.2.2
                                          linarith only [hc14, hlam, hphi, ht0b, ht45, ht5b, p150_1, u0elo0]
                                        · have p150_0 := h150c.1
                                          have p150_1 := h150c.2.1
                                          have p150_2 := h150c.2.2.1
                                          have p150_3 := h150c.2.2.2
                                          linarith only [hc15, hlam, hphi, ht0b, ht5b, p150_1, u0elo0]
                                        · have p150_0 := h150c.1
                                          have p150_1 := h150c.2.1
                                          have p150_2 := h150c.2.2.1
                                          have p150_3 := h150c.2.2.2
                                          linarith only [h0, hlam, p150_0]
                                        · have p150_0 := h150c.1
                                          have p150_1 := h150c.2.1
                                          have p150_2 := h150c.2.2.1
                                          have p150_3 := h150c.2.2.2
                                          linarith only [hlam, p150_0]
                                        · have p150_0 := h150c.1
                                          have p150_1 := h150c.2.1
                                          have p150_2 := h150c.2.2.1
                                          have p150_3 := h150c.2.2.2
                                          linarith only [h130, hlam, p150_0]
                                        · have p150_0 := h150c.1
                                          have p150_1 := h150c.2.1
                                          have p150_2 := h150c.2.2.1
                                          have p150_3 := h150c.2.2.2
                                          linarith only [h132, hlam, p150_0]
                                        · have p150_0 := h150c.1
                                          have p150_1 := h150c.2.1
                                          have p150_2 := h150c.2.2.1
                                          have p150_3 := h150c.2.2.2
                                          linarith only [h134, hlam, p150_0]
                                        · have p150_0 := h150c.1
                                          have p150_1 := h150c.2.1
                                          have p150_2 := h150c.2.2.1
                                          have p150_3 := h150c.2.2.2
                                          linarith only [h1, hlam, p150_0]
                                        · have p150_0 := h150c.1
                                          have p150_1 := h150c.2.1
                                          have p150_2 := h150c.2.2.1
                                          have p150_3 := h150c.2.2.2
                                          linarith only [h1, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p150_1, u0elo0]
                                        · have p150_0 := h150c.1
                                          have p150_1 := h150c.2.1
                                          have p150_2 := h150c.2.2.1
                                          have p150_3 := h150c.2.2.2
                                          linarith only [hlam, p150_0]
                                        · have p150_0 := h150c.1
                                          have p150_1 := h150c.2.1
                                          have p150_2 := h150c.2.2.1
                                          have p150_3 := h150c.2.2.2
                                          linarith only [h136, hlam, p150_1]
                                        · have p150_0 := h150c.1
                                          have p150_1 := h150c.2.1
                                          have p150_2 := h150c.2.2.1
                                          have p150_3 := h150c.2.2.2
                                          linarith only [h138, hlam, p150_1]
                                        · have p150_0 := h150c.1
                                          have p150_1 := h150c.2.1
                                          have p150_2 := h150c.2.2.1
                                          have p150_3 := h150c.2.2.2
                                          linarith only [h2, hlam, p150_0]
                                        · have p150_0 := h150c.1
                                          have p150_1 := h150c.2.1
                                          have p150_2 := h150c.2.2.1
                                          have p150_3 := h150c.2.2.2
                                          linarith only [h2, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p150_1, u0elo0]
                                        · have p150_0 := h150c.1
                                          have p150_1 := h150c.2.1
                                          have p150_2 := h150c.2.2.1
                                          have p150_3 := h150c.2.2.2
                                          linarith only [h2, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p150_1, u0elo3]
                                        · have p150_0 := h150c.1
                                          have p150_1 := h150c.2.1
                                          have p150_2 := h150c.2.2.1
                                          have p150_3 := h150c.2.2.2
                                          linarith only [hlam, p150_0]
                                        · have p150_0 := h150c.1
                                          have p150_1 := h150c.2.1
                                          have p150_2 := h150c.2.2.1
                                          have p150_3 := h150c.2.2.2
                                          linarith only [h140, hlam, p150_1]
                                        · have p150_0 := h150c.1
                                          have p150_1 := h150c.2.1
                                          have p150_2 := h150c.2.2.1
                                          have p150_3 := h150c.2.2.2
                                          linarith only [h3, hlam, p150_0]
                                        · have p150_0 := h150c.1
                                          have p150_1 := h150c.2.1
                                          have p150_2 := h150c.2.2.1
                                          have p150_3 := h150c.2.2.2
                                          linarith only [h3, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p150_1, u0elo0]
                                        · have p150_0 := h150c.1
                                          have p150_1 := h150c.2.1
                                          have p150_2 := h150c.2.2.1
                                          have p150_3 := h150c.2.2.2
                                          linarith only [h130, h3, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p150_1, u0elo0]
                                        · have p150_0 := h150c.1
                                          have p150_1 := h150c.2.1
                                          have p150_2 := h150c.2.2.1
                                          have p150_3 := h150c.2.2.2
                                          linarith only [h3, hc14, hlam, hphi, ht0b, ht45, ht5b, p150_1, u0elo0]
                                        · have p150_0 := h150c.1
                                          have p150_1 := h150c.2.1
                                          have p150_2 := h150c.2.2.1
                                          have p150_3 := h150c.2.2.2
                                          linarith only [hlam, p150_0]
                                  · linarith only [h0, h142, h143, h4, h70, hc12, hc35, hlam, hphi, ht23]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h177 | h177
                                  · linarith only [h0, h102, h142, h177, h4, hc12, hc34, hlam, hphi, ht23]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h179 | h179
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h180 | h180
                                      · rcases h1bigk with h181c | h181c | h181c | h181c | h181c | h181c | h181c | h181c | h181c | h181c | h181c | h181c | h181c | h181c | h181c | h181c | h181c | h181c | h181c | h181c | h181c | h181c | h181c | h181c | h181c
                                        · have p181_0 := h181c.1
                                          have p181_1 := h181c.2.1
                                          have p181_2 := h181c.2.2.1
                                          have p181_3 := h181c.2.2.2
                                          linarith only [hlam, p181_0]
                                        · have p181_0 := h181c.1
                                          have p181_1 := h181c.2.1
                                          have p181_2 := h181c.2.2.1
                                          have p181_3 := h181c.2.2.2
                                          linarith only [hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p181_1, u0elo0]
                                        · have p181_0 := h181c.1
                                          have p181_1 := h181c.2.1
                                          have p181_2 := h181c.2.2.1
                                          have p181_3 := h181c.2.2.2
                                          linarith only [h130, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p181_1, u0elo0]
                                        · have p181_0 := h181c.1
                                          have p181_1 := h181c.2.1
                                          have p181_2 := h181c.2.2.1
                                          have p181_3 := h181c.2.2.2
                                          linarith only [h130, h136, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p181_1, u0elo0]
                                        · have p181_0 := h181c.1
                                          have p181_1 := h181c.2.1
                                          have p181_2 := h181c.2.2.1
                                          have p181_3 := h181c.2.2.2
                                          linarith only [hc15, hlam, hphi, ht0b, ht5b, p181_1, u0elo0]
                                        · have p181_0 := h181c.1
                                          have p181_1 := h181c.2.1
                                          have p181_2 := h181c.2.2.1
                                          have p181_3 := h181c.2.2.2
                                          linarith only [h0, hlam, p181_0]
                                        · have p181_0 := h181c.1
                                          have p181_1 := h181c.2.1
                                          have p181_2 := h181c.2.2.1
                                          have p181_3 := h181c.2.2.2
                                          linarith only [hlam, p181_0]
                                        · have p181_0 := h181c.1
                                          have p181_1 := h181c.2.1
                                          have p181_2 := h181c.2.2.1
                                          have p181_3 := h181c.2.2.2
                                          linarith only [h130, hlam, p181_0]
                                        · have p181_0 := h181c.1
                                          have p181_1 := h181c.2.1
                                          have p181_2 := h181c.2.2.1
                                          have p181_3 := h181c.2.2.2
                                          linarith only [h132, hlam, p181_0]
                                        · have p181_0 := h181c.1
                                          have p181_1 := h181c.2.1
                                          have p181_2 := h181c.2.2.1
                                          have p181_3 := h181c.2.2.2
                                          linarith only [h134, hlam, p181_0]
                                        · have p181_0 := h181c.1
                                          have p181_1 := h181c.2.1
                                          have p181_2 := h181c.2.2.1
                                          have p181_3 := h181c.2.2.2
                                          linarith only [h1, hlam, p181_0]
                                        · have p181_0 := h181c.1
                                          have p181_1 := h181c.2.1
                                          have p181_2 := h181c.2.2.1
                                          have p181_3 := h181c.2.2.2
                                          linarith only [h136, h2, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p181_1, u0elo3]
                                        · have p181_0 := h181c.1
                                          have p181_1 := h181c.2.1
                                          have p181_2 := h181c.2.2.1
                                          have p181_3 := h181c.2.2.2
                                          linarith only [hlam, p181_0]
                                        · have p181_0 := h181c.1
                                          have p181_1 := h181c.2.1
                                          have p181_2 := h181c.2.2.1
                                          have p181_3 := h181c.2.2.2
                                          linarith only [h136, hlam, p181_1]
                                        · have p181_0 := h181c.1
                                          have p181_1 := h181c.2.1
                                          have p181_2 := h181c.2.2.1
                                          have p181_3 := h181c.2.2.2
                                          linarith only [h138, hlam, p181_1]
                                        · have p181_0 := h181c.1
                                          have p181_1 := h181c.2.1
                                          have p181_2 := h181c.2.2.1
                                          have p181_3 := h181c.2.2.2
                                          linarith only [h2, hlam, p181_0]
                                        · have p181_0 := h181c.1
                                          have p181_1 := h181c.2.1
                                          have p181_2 := h181c.2.2.1
                                          have p181_3 := h181c.2.2.2
                                          linarith only [h2, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p181_1, u0elo0]
                                        · have p181_0 := h181c.1
                                          have p181_1 := h181c.2.1
                                          have p181_2 := h181c.2.2.1
                                          have p181_3 := h181c.2.2.2
                                          linarith only [h2, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p181_1, u0elo0]
                                        · have p181_0 := h181c.1
                                          have p181_1 := h181c.2.1
                                          have p181_2 := h181c.2.2.1
                                          have p181_3 := h181c.2.2.2
                                          linarith only [hlam, p181_0]
                                        · have p181_0 := h181c.1
                                          have p181_1 := h181c.2.1
                                          have p181_2 := h181c.2.2.1
                                          have p181_3 := h181c.2.2.2
                                          linarith only [h140, hlam, p181_1]
                                        · have p181_0 := h181c.1
                                          have p181_1 := h181c.2.1
                                          have p181_2 := h181c.2.2.1
                                          have p181_3 := h181c.2.2.2
                                          linarith only [h3, hlam, p181_0]
                                        · have p181_0 := h181c.1
                                          have p181_1 := h181c.2.1
                                          have p181_2 := h181c.2.2.1
                                          have p181_3 := h181c.2.2.2
                                          linarith only [h3, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p181_1, u0elo0]
                                        · have p181_0 := h181c.1
                                          have p181_1 := h181c.2.1
                                          have p181_2 := h181c.2.2.1
                                          have p181_3 := h181c.2.2.2
                                          linarith only [h130, h3, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p181_1, u0elo0]
                                        · have p181_0 := h181c.1
                                          have p181_1 := h181c.2.1
                                          have p181_2 := h181c.2.2.1
                                          have p181_3 := h181c.2.2.2
                                          linarith only [h3, hc14, hlam, hphi, ht0b, ht45, ht5b, p181_1, u0elo0]
                                        · have p181_0 := h181c.1
                                          have p181_1 := h181c.2.1
                                          have p181_2 := h181c.2.2.1
                                          have p181_3 := h181c.2.2.2
                                          linarith only [hlam, p181_0]
                                      · linarith only [h142, h179, h180, hlam]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h208 | h208
                                      · linarith only [h0, h142, h179, h208, h4, hc12, hc34, hlam, hphi, ht23]
                                      · linarith only [h0, h142, h208, h4, hc12, hc45, hlam, hphi, ht23, ht34]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h211 | h211
          · rcases m.htr 0 2 4 (by decide) (by decide) with h212 | h212
            · rcases m.htr 0 3 4 (by decide) (by decide) with h213 | h213
              · rcases m.htr 0 3 5 (by decide) (by decide) with h214 | h214
                · linarith only [h1, h214, h3, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h216 | h216
                  · linarith only [h2, h216, h3, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h218 | h218
                    · linarith only [h0, h218, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · linarith only [h211, h218, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h221 | h221
                · linarith only [h0, h212, h213, h221, h3, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h223 | h223
                  · linarith only [h0, h212, h223, h3, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h225 | h225
                    · linarith only [h0, h225, h3, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo4]
                    · linarith only [h0, h211, h225, h3, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo4]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h228 | h228
              · linarith only [h211, h212, h228, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h230 | h230
                · linarith only [h2, h211, h212, h230, h3, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h232 | h232
                  · linarith only [h2, h232, h3, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h234 | h234
                    · linarith only [h0, h234, h3, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo4]
                    · linarith only [h2, h211, h212, h234, h3, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo4]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h237 | h237
            · rcases m.htr 0 3 4 (by decide) (by decide) with h238 | h238
              · rcases m.htr 0 3 5 (by decide) (by decide) with h239 | h239
                · linarith only [h1, h239, h3, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h241 | h241
                  · linarith only [h0, h237, h241, h3, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h243 | h243
                    · linarith only [h0, h211, h243, h3, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo4]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h245 | h245
                      · linarith only [h0, h245, h3, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo4]
                      · linarith only [h237, h245, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
              · linarith only [h211, h237, h238, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h249 | h249
              · rcases m.htr 0 3 5 (by decide) (by decide) with h250 | h250
                · linarith only [h1, h250, h3, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h252 | h252
                  · linarith only [h1, h249, h252, h3, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h254 | h254
                    · linarith only [h0, h211, h254, h3, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo4]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h256 | h256
                      · linarith only [h0, h237, h256, h3, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo4]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h258 | h258
                        · linarith only [h1, h254, h258, h3, hc25, hlam, hphi, ht0b, ht5b, u0elo4]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h260 | h260
                          · linarith only [h1, h260, h3, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo4]
                          · linarith only [h1, h249, h254, h260, h3, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo4]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h263 | h263
                · linarith only [h2, h249, h263, h3, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h265 | h265
                  · linarith only [h2, h265, h3, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h267 | h267
                    · linarith only [h0, h211, h267, h3, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo4]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h269 | h269
                      · linarith only [h0, h237, h249, h269, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h271 | h271
                        · linarith only [h0, h271, h3, hc25, hlam, hphi, ht0b, ht5b, u0elo4]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h273 | h273
                          · linarith only [h1, h249, h273, h3, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo4]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h275 | h275
                            · linarith only [h2, h263, h273, h275, h3, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h277 | h277
                              · linarith only [h2, h265, h277, h3, hlam]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h279 | h279
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h280 | h280
                                  · linarith only [h2, h267, h273, h275, h280, h3, hc12, hc23, hlam, hphi]
                                  · linarith only [h0, h211, h249, h279, h280, hc12, hc35, hlam, hphi, ht23]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h283 | h283
                                  · linarith only [h0, h211, h263, h279, h283, hc12, hc34, hlam, hphi, ht23]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h285 | h285
                                    · linarith only [h2, h267, h273, h277, h285, h3, hc12, hc24, hlam, hphi]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h287 | h287
                                      · linarith only [h0, h211, h279, h285, h287, hc12, hc34, hlam, hphi, ht23]
                                      · linarith only [h0, h211, h279, h287, hc12, hc45, hlam, hphi, ht23, ht34]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h290 | h290
        · rcases m.htr 0 2 3 (by decide) (by decide) with h291 | h291
          · rcases m.htr 0 2 4 (by decide) (by decide) with h292 | h292
            · linarith only [h0, h2, h292, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h294 | h294
              · linarith only [h1, h2, h294, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h296 | h296
                · rcases m.htr 0 4 5 (by decide) (by decide) with h297 | h297
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h298 | h298
                    · linarith only [h0, h298, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · linarith only [h0, h2, h291, h298, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3]
                  · linarith only [h0, h2, h291, h296, h297, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h302 | h302
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h303 | h303
                    · linarith only [h0, h2, h303, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                    · linarith only [h0, h2, h291, h303, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3]
                  · linarith only [h2, h290, h302, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h307 | h307
            · linarith only [h1, h2, h291, h307, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h309 | h309
              · linarith only [h1, h2, h309, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h311 | h311
                · rcases m.htr 0 4 5 (by decide) (by decide) with h312 | h312
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h313 | h313
                    · linarith only [h0, h2, h291, h313, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h315 | h315
                      · linarith only [h0, h1, h2, h307, h315, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h317 | h317
                        · linarith only [h1, h313, h317, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h319 | h319
                          · linarith only [h1, h2, h291, h309, h319, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h321 | h321
                            · linarith only [h1, h2, h321, hc35, hlam, hphi, ht0b, ht5b, u0elo3]
                            · linarith only [h311, h313, h321, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                  · linarith only [h1, h2, h311, h312, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h325 | h325
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h326 | h326
                    · linarith only [h0, h291, h326, hlam]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h328 | h328
                      · linarith only [h1, h326, h328, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo0]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h330 | h330
                        · linarith only [h1, h326, h330, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h332 | h332
                          · linarith only [h1, h2, h309, h332, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo3]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h334 | h334
                            · linarith only [h1, h311, h334, hlam]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h336 | h336
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h337 | h337
                                · linarith only [h2, h290, h326, h332, h334, h337, hc12, hc23, hlam, hphi]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h339 | h339
                                  · linarith only [h1, h311, h326, h337, h339, hc12, hc34, hlam, hphi, ht23]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h341 | h341
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h342 | h342
                                      · rcases h1bigk with h343c | h343c | h343c | h343c | h343c | h343c | h343c | h343c | h343c | h343c | h343c | h343c | h343c | h343c | h343c | h343c | h343c | h343c | h343c | h343c | h343c | h343c | h343c | h343c | h343c
                                        · have p343_0 := h343c.1
                                          have p343_1 := h343c.2.1
                                          have p343_2 := h343c.2.2.1
                                          have p343_3 := h343c.2.2.2
                                          linarith only [hlam, p343_0]
                                        · have p343_0 := h343c.1
                                          have p343_1 := h343c.2.1
                                          have p343_2 := h343c.2.2.1
                                          have p343_3 := h343c.2.2.2
                                          linarith only [h2, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p343_1, u0elo3]
                                        · have p343_0 := h343c.1
                                          have p343_1 := h343c.2.1
                                          have p343_2 := h343c.2.2.1
                                          have p343_3 := h343c.2.2.2
                                          linarith only [h2, h326, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p343_1, u0elo3]
                                        · have p343_0 := h343c.1
                                          have p343_1 := h343c.2.1
                                          have p343_2 := h343c.2.2.1
                                          have p343_3 := h343c.2.2.2
                                          linarith only [h2, hlam, p343_0]
                                        · have p343_0 := h343c.1
                                          have p343_1 := h343c.2.1
                                          have p343_2 := h343c.2.2.1
                                          have p343_3 := h343c.2.2.2
                                          linarith only [h2, hc15, hlam, hphi, ht0b, ht5b, p343_1, u0elo3]
                                        · have p343_0 := h343c.1
                                          have p343_1 := h343c.2.1
                                          have p343_2 := h343c.2.2.1
                                          have p343_3 := h343c.2.2.2
                                          linarith only [h0, hlam, p343_0]
                                        · have p343_0 := h343c.1
                                          have p343_1 := h343c.2.1
                                          have p343_2 := h343c.2.2.1
                                          have p343_3 := h343c.2.2.2
                                          linarith only [hlam, p343_0]
                                        · have p343_0 := h343c.1
                                          have p343_1 := h343c.2.1
                                          have p343_2 := h343c.2.2.1
                                          have p343_3 := h343c.2.2.2
                                          linarith only [h326, hlam, p343_0]
                                        · have p343_0 := h343c.1
                                          have p343_1 := h343c.2.1
                                          have p343_2 := h343c.2.2.1
                                          have p343_3 := h343c.2.2.2
                                          linarith only [h328, hlam, p343_0]
                                        · have p343_0 := h343c.1
                                          have p343_1 := h343c.2.1
                                          have p343_2 := h343c.2.2.1
                                          have p343_3 := h343c.2.2.2
                                          linarith only [h330, hlam, p343_0]
                                        · have p343_0 := h343c.1
                                          have p343_1 := h343c.2.1
                                          have p343_2 := h343c.2.2.1
                                          have p343_3 := h343c.2.2.2
                                          linarith only [h1, hlam, p343_0]
                                        · have p343_0 := h343c.1
                                          have p343_1 := h343c.2.1
                                          have p343_2 := h343c.2.2.1
                                          have p343_3 := h343c.2.2.2
                                          linarith only [h1, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p343_1, u0elo2]
                                        · have p343_0 := h343c.1
                                          have p343_1 := h343c.2.1
                                          have p343_2 := h343c.2.2.1
                                          have p343_3 := h343c.2.2.2
                                          linarith only [hlam, p343_0]
                                        · have p343_0 := h343c.1
                                          have p343_1 := h343c.2.1
                                          have p343_2 := h343c.2.2.1
                                          have p343_3 := h343c.2.2.2
                                          linarith only [h332, hlam, p343_1]
                                        · have p343_0 := h343c.1
                                          have p343_1 := h343c.2.1
                                          have p343_2 := h343c.2.2.1
                                          have p343_3 := h343c.2.2.2
                                          linarith only [h334, hlam, p343_1]
                                        · have p343_0 := h343c.1
                                          have p343_1 := h343c.2.1
                                          have p343_2 := h343c.2.2.1
                                          have p343_3 := h343c.2.2.2
                                          linarith only [h0, h328, hc12, hc24, hlam, hphi, p343_1]
                                        · have p343_0 := h343c.1
                                          have p343_1 := h343c.2.1
                                          have p343_2 := h343c.2.2.1
                                          have p343_3 := h343c.2.2.2
                                          rcases p343_3 (m.d 0 1) (by simp) with h360 | h360
                                          · linarith only [h2, h360, hlam]
                                          · linarith only [h0, h360, hlam]
                                        · have p343_0 := h343c.1
                                          have p343_1 := h343c.2.1
                                          have p343_2 := h343c.2.2.1
                                          have p343_3 := h343c.2.2.2
                                          rcases p343_3 (m.d 0 1) (by simp) with h363 | h363
                                          · linarith only [h2, h363, hlam]
                                          · linarith only [h1, h363, hlam]
                                        · have p343_0 := h343c.1
                                          have p343_1 := h343c.2.1
                                          have p343_2 := h343c.2.2.1
                                          have p343_3 := h343c.2.2.2
                                          linarith only [hlam, p343_0]
                                        · have p343_0 := h343c.1
                                          have p343_1 := h343c.2.1
                                          have p343_2 := h343c.2.2.1
                                          have p343_3 := h343c.2.2.2
                                          rcases p343_3 (m.d 0 1) (by simp) with h367 | h367
                                          · linarith only [h2, h367, hlam]
                                          · linarith only [h290, h367, hlam]
                                        · have p343_0 := h343c.1
                                          have p343_1 := h343c.2.1
                                          have p343_2 := h343c.2.2.1
                                          have p343_3 := h343c.2.2.2
                                          linarith only [h290, hlam, p343_0]
                                        · have p343_0 := h343c.1
                                          have p343_1 := h343c.2.1
                                          have p343_2 := h343c.2.2.1
                                          have p343_3 := h343c.2.2.2
                                          linarith only [h2, h290, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p343_1, u0elo3]
                                        · have p343_0 := h343c.1
                                          have p343_1 := h343c.2.1
                                          have p343_2 := h343c.2.2.1
                                          have p343_3 := h343c.2.2.2
                                          linarith only [h2, h290, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, p343_1, u0elo3]
                                        · have p343_0 := h343c.1
                                          have p343_1 := h343c.2.1
                                          have p343_2 := h343c.2.2.1
                                          have p343_3 := h343c.2.2.2
                                          linarith only [h336, hlam, p343_0]
                                        · have p343_0 := h343c.1
                                          have p343_1 := h343c.2.1
                                          have p343_2 := h343c.2.2.1
                                          have p343_3 := h343c.2.2.2
                                          linarith only [hlam, p343_0]
                                      · linarith only [h0, h2, h328, h337, h342, hc12, hc45, hlam, hphi, ht23, ht34]
                                    · linarith only [h2, h290, h328, h336, h341, hlam]
                              · linarith only [h2, h290, h326, h334, h336, hc12, hc45, hlam, hphi, ht23, ht34]
                  · linarith only [h2, h290, h325, hlam]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h379 | h379
          · rcases m.htr 0 2 4 (by decide) (by decide) with h380 | h380
            · linarith only [h0, h2, h380, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h382 | h382
              · linarith only [h1, h2, h382, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h384 | h384
                · linarith only [h0, h290, h379, h384, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h386 | h386
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h387 | h387
                    · linarith only [h0, h387, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · linarith only [h0, h290, h379, h386, h387, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h390 | h390
                    · linarith only [h0, h390, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · linarith only [h0, h2, h379, h386, h390, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo4]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h393 | h393
            · linarith only [h1, h2, h379, h393, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h395 | h395
              · linarith only [h1, h2, h395, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h397 | h397
                · linarith only [h1, h290, h397, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h399 | h399
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h400 | h400
                    · linarith only [h0, h290, h379, h399, h400, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h402 | h402
                      · linarith only [h0, h1, h290, h393, h399, h402, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo1]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h404 | h404
                        · linarith only [h1, h400, h404, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h406 | h406
                          · linarith only [h1, h290, h379, h395, h399, h406, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h408 | h408
                            · linarith only [h0, h1, h290, h397, h408, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h410 | h410
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h411 | h411
                                · linarith only [h1, h290, h400, h406, h410, h411, hc12, hc23, hlam, hphi]
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h413 | h413
                                  · linarith only [h1, h290, h400, h408, h413, hc12, hc23, hlam, hphi]
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h415 | h415
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h416 | h416
                                      · rcases h1bigk with h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c | h417c
                                        · have p417_0 := h417c.1
                                          have p417_1 := h417c.2.1
                                          have p417_2 := h417c.2.2.1
                                          have p417_3 := h417c.2.2.2
                                          linarith only [hlam, p417_0]
                                        · have p417_0 := h417c.1
                                          have p417_1 := h417c.2.1
                                          have p417_2 := h417c.2.2.1
                                          have p417_3 := h417c.2.2.2
                                          linarith only [hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p417_1, u0elo0]
                                        · have p417_0 := h417c.1
                                          have p417_1 := h417c.2.1
                                          have p417_2 := h417c.2.2.1
                                          have p417_3 := h417c.2.2.2
                                          linarith only [h290, h399, h400, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p417_1, u0elo3]
                                        · have p417_0 := h417c.1
                                          have p417_1 := h417c.2.1
                                          have p417_2 := h417c.2.2.1
                                          have p417_3 := h417c.2.2.2
                                          linarith only [h2, hlam, p417_0]
                                        · have p417_0 := h417c.1
                                          have p417_1 := h417c.2.1
                                          have p417_2 := h417c.2.2.1
                                          have p417_3 := h417c.2.2.2
                                          linarith only [h290, hlam, p417_0]
                                        · have p417_0 := h417c.1
                                          have p417_1 := h417c.2.1
                                          have p417_2 := h417c.2.2.1
                                          have p417_3 := h417c.2.2.2
                                          linarith only [h0, hlam, p417_0]
                                        · have p417_0 := h417c.1
                                          have p417_1 := h417c.2.1
                                          have p417_2 := h417c.2.2.1
                                          have p417_3 := h417c.2.2.2
                                          linarith only [hlam, p417_0]
                                        · have p417_0 := h417c.1
                                          have p417_1 := h417c.2.1
                                          have p417_2 := h417c.2.2.1
                                          have p417_3 := h417c.2.2.2
                                          linarith only [h400, hlam, p417_0]
                                        · have p417_0 := h417c.1
                                          have p417_1 := h417c.2.1
                                          have p417_2 := h417c.2.2.1
                                          have p417_3 := h417c.2.2.2
                                          linarith only [h402, hlam, p417_0]
                                        · have p417_0 := h417c.1
                                          have p417_1 := h417c.2.1
                                          have p417_2 := h417c.2.2.1
                                          have p417_3 := h417c.2.2.2
                                          linarith only [h404, hlam, p417_0]
                                        · have p417_0 := h417c.1
                                          have p417_1 := h417c.2.1
                                          have p417_2 := h417c.2.2.1
                                          have p417_3 := h417c.2.2.2
                                          linarith only [h1, hlam, p417_0]
                                        · have p417_0 := h417c.1
                                          have p417_1 := h417c.2.1
                                          have p417_2 := h417c.2.2.1
                                          have p417_3 := h417c.2.2.2
                                          linarith only [h1, h290, h399, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p417_1, u0elo3]
                                        · have p417_0 := h417c.1
                                          have p417_1 := h417c.2.1
                                          have p417_2 := h417c.2.2.1
                                          have p417_3 := h417c.2.2.2
                                          linarith only [hlam, p417_0]
                                        · have p417_0 := h417c.1
                                          have p417_1 := h417c.2.1
                                          have p417_2 := h417c.2.2.1
                                          have p417_3 := h417c.2.2.2
                                          linarith only [h406, hlam, p417_1]
                                        · have p417_0 := h417c.1
                                          have p417_1 := h417c.2.1
                                          have p417_2 := h417c.2.2.1
                                          have p417_3 := h417c.2.2.2
                                          linarith only [h408, hlam, p417_1]
                                        · have p417_0 := h417c.1
                                          have p417_1 := h417c.2.1
                                          have p417_2 := h417c.2.2.1
                                          have p417_3 := h417c.2.2.2
                                          linarith only [h0, h402, hc12, hc24, hlam, hphi, p417_1]
                                        · have p417_0 := h417c.1
                                          have p417_1 := h417c.2.1
                                          have p417_2 := h417c.2.2.1
                                          have p417_3 := h417c.2.2.2
                                          rcases p417_3 (m.d 0 1) (by simp) with h434 | h434
                                          · linarith only [h2, h434, hlam]
                                          · linarith only [h0, h434, hlam]
                                        · have p417_0 := h417c.1
                                          have p417_1 := h417c.2.1
                                          have p417_2 := h417c.2.2.1
                                          have p417_3 := h417c.2.2.2
                                          rcases p417_3 (m.d 0 1) (by simp) with h437 | h437
                                          · linarith only [h2, h437, hlam]
                                          · linarith only [h1, h437, hlam]
                                        · have p417_0 := h417c.1
                                          have p417_1 := h417c.2.1
                                          have p417_2 := h417c.2.2.1
                                          have p417_3 := h417c.2.2.2
                                          linarith only [hlam, p417_0]
                                        · have p417_0 := h417c.1
                                          have p417_1 := h417c.2.1
                                          have p417_2 := h417c.2.2.1
                                          have p417_3 := h417c.2.2.2
                                          linarith only [h1, h290, h400, h402, h411, hc12, hc34, hlam, hphi, ht23, p417_1]
                                        · have p417_0 := h417c.1
                                          have p417_1 := h417c.2.1
                                          have p417_2 := h417c.2.2.1
                                          have p417_3 := h417c.2.2.2
                                          linarith only [h1, h400, h404, hc12, hc25, hlam, hphi, p417_1]
                                        · have p417_0 := h417c.1
                                          have p417_1 := h417c.2.1
                                          have p417_2 := h417c.2.2.1
                                          have p417_3 := h417c.2.2.2
                                          rcases p417_3 (m.d 0 1) (by simp) with h443 | h443
                                          · linarith only [h290, h443, hlam]
                                          · linarith only [h0, h443, hlam]
                                        · have p417_0 := h417c.1
                                          have p417_1 := h417c.2.1
                                          have p417_2 := h417c.2.2.1
                                          have p417_3 := h417c.2.2.2
                                          rcases p417_3 (m.d 0 1) (by simp) with h446 | h446
                                          · linarith only [h290, h446, hlam]
                                          · linarith only [h1, h446, hlam]
                                        · have p417_0 := h417c.1
                                          have p417_1 := h417c.2.1
                                          have p417_2 := h417c.2.2.1
                                          have p417_3 := h417c.2.2.2
                                          linarith only [h410, hlam, p417_0]
                                        · have p417_0 := h417c.1
                                          have p417_1 := h417c.2.1
                                          have p417_2 := h417c.2.2.1
                                          have p417_3 := h417c.2.2.2
                                          linarith only [hlam, p417_0]
                                      · linarith only [h1, h2, h400, h402, h411, h416, hc12, hc45, hlam, hphi, ht23, ht34]
                                    · linarith only [h1, h290, h399, h400, h402, h410, h415, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3]
                              · linarith only [h399, h410, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h454 | h454
                    · linarith only [h0, h454, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h456 | h456
                      · linarith only [h1, h2, h393, h399, h454, h456, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo4]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h458 | h458
                        · linarith only [h0, h2, h399, h458, hc25, hlam, hphi, ht0b, ht5b, u0elo4]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h460 | h460
                          · linarith only [h1, h2, h395, h399, h460, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo4]
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h462 | h462
                            · linarith only [h1, h2, h399, h462, hc35, hlam, hphi, ht0b, ht5b, u0elo4]
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h464 | h464
                              · linarith only [h1, h2, h399, h454, h456, h464, hc12, hc24, hlam, hphi]
                              · linarith only [h1, h2, h454, h464, hc12, hc45, hlam, hphi, ht23, ht34]
    · rcases m.htr 0 1 4 (by decide) (by decide) with h467 | h467
      · rcases m.htr 0 1 5 (by decide) (by decide) with h468 | h468
        · rcases m.htr 0 2 3 (by decide) (by decide) with h469 | h469
          · linarith only [h0, h1, h469, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h471 | h471
            · rcases m.htr 0 3 4 (by decide) (by decide) with h472 | h472
              · rcases m.htr 0 3 5 (by decide) (by decide) with h473 | h473
                · rcases m.htr 0 4 5 (by decide) (by decide) with h474 | h474
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h475 | h475
                    · linarith only [h0, h469, h475, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h477 | h477
                      · linarith only [h0, h1, h477, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                      · linarith only [h471, h477, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h480 | h480
                    · linarith only [h0, h1, h469, h480, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h482 | h482
                      · linarith only [h0, h1, h482, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                      · linarith only [h471, h482, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                · linarith only [h1, h468, h473, hlam]
              · linarith only [h0, h1, h471, h472, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h487 | h487
              · rcases m.htr 0 3 5 (by decide) (by decide) with h488 | h488
                · rcases m.htr 0 4 5 (by decide) (by decide) with h489 | h489
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h490 | h490
                    · linarith only [h0, h1, h469, h490, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h492 | h492
                      · linarith only [h0, h471, h489, h492, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h494 | h494
                        · linarith only [h1, h467, h492, h494, hc25, hlam, hphi, ht0b, ht5b, u0elo2]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h496 | h496
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h497 | h497
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h498 | h498
                              · linarith only [h1, h467, h498, hc45, hlam, hphi, ht0b, ht5b, u0elo2]
                              · linarith only [h489, h492, h498, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo3]
                            · linarith only [h0, h1, h497, hc12, hc35, hlam, hphi, ht23]
                          · linarith only [h1, h487, h496, hc01, hlam, hphi, ht0b, ht12, ht23, ht34, ht45, ht5b, u0elo2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h503 | h503
                    · linarith only [h0, h469, h503, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h505 | h505
                      · linarith only [h0, h471, h505, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h507 | h507
                        · linarith only [h1, h467, h505, h507, hc25, hlam, hphi, ht0b, ht5b, u0elo2]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h509 | h509
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h510 | h510
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h511 | h511
                              · linarith only [h0, h1, h467, h471, h489, h511, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h513 | h513
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h514 | h514
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h515 | h515
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h516 | h516
                                      · linarith only [h467, h489, h509, h516, hlam]
                                      · rcases h1bigk with h518c | h518c | h518c | h518c | h518c | h518c | h518c | h518c | h518c | h518c | h518c | h518c | h518c | h518c | h518c | h518c | h518c | h518c | h518c | h518c | h518c | h518c | h518c | h518c | h518c
                                        · have p518_0 := h518c.1
                                          have p518_1 := h518c.2.1
                                          have p518_2 := h518c.2.2.1
                                          have p518_3 := h518c.2.2.2
                                          linarith only [hlam, p518_0]
                                        · have p518_0 := h518c.1
                                          have p518_1 := h518c.2.1
                                          have p518_2 := h518c.2.2.1
                                          have p518_3 := h518c.2.2.2
                                          linarith only [h1, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p518_1, u0elo2]
                                        · have p518_0 := h518c.1
                                          have p518_1 := h518c.2.1
                                          have p518_2 := h518c.2.2.1
                                          have p518_3 := h518c.2.2.2
                                          linarith only [h1, hlam, p518_0]
                                        · have p518_0 := h518c.1
                                          have p518_1 := h518c.2.1
                                          have p518_2 := h518c.2.2.1
                                          have p518_3 := h518c.2.2.2
                                          linarith only [h1, hc14, hlam, hphi, ht0b, ht45, ht5b, p518_1, u0elo2]
                                        · have p518_0 := h518c.1
                                          have p518_1 := h518c.2.1
                                          have p518_2 := h518c.2.2.1
                                          have p518_3 := h518c.2.2.2
                                          linarith only [h1, hc15, hlam, hphi, ht0b, ht5b, p518_1, u0elo2]
                                        · have p518_0 := h518c.1
                                          have p518_1 := h518c.2.1
                                          have p518_2 := h518c.2.2.1
                                          have p518_3 := h518c.2.2.2
                                          linarith only [h0, hlam, p518_0]
                                        · have p518_0 := h518c.1
                                          have p518_1 := h518c.2.1
                                          have p518_2 := h518c.2.2.1
                                          have p518_3 := h518c.2.2.2
                                          linarith only [hlam, p518_0]
                                        · have p518_0 := h518c.1
                                          have p518_1 := h518c.2.1
                                          have p518_2 := h518c.2.2.1
                                          have p518_3 := h518c.2.2.2
                                          linarith only [h503, hlam, p518_0]
                                        · have p518_0 := h518c.1
                                          have p518_1 := h518c.2.1
                                          have p518_2 := h518c.2.2.1
                                          have p518_3 := h518c.2.2.2
                                          linarith only [h505, hlam, p518_0]
                                        · have p518_0 := h518c.1
                                          have p518_1 := h518c.2.1
                                          have p518_2 := h518c.2.2.1
                                          have p518_3 := h518c.2.2.2
                                          linarith only [h507, hlam, p518_0]
                                        · have p518_0 := h518c.1
                                          have p518_1 := h518c.2.1
                                          have p518_2 := h518c.2.2.1
                                          have p518_3 := h518c.2.2.2
                                          linarith only [h0, h503, hc12, hc23, hlam, hphi, p518_1]
                                        · have p518_0 := h518c.1
                                          have p518_1 := h518c.2.1
                                          have p518_2 := h518c.2.2.1
                                          have p518_3 := h518c.2.2.2
                                          rcases p518_3 (m.d 0 1) (by simp) with h530 | h530
                                          · linarith only [h1, h530, hlam]
                                          · linarith only [h0, h530, hlam]
                                        · have p518_0 := h518c.1
                                          have p518_1 := h518c.2.1
                                          have p518_2 := h518c.2.2.1
                                          have p518_3 := h518c.2.2.2
                                          linarith only [hlam, p518_0]
                                        · have p518_0 := h518c.1
                                          have p518_1 := h518c.2.1
                                          have p518_2 := h518c.2.2.1
                                          have p518_3 := h518c.2.2.2
                                          rcases p518_3 (m.d 0 1) (by simp) with h534 | h534
                                          · linarith only [h1, h534, hlam]
                                          · linarith only [h467, h534, hlam]
                                        · have p518_0 := h518c.1
                                          have p518_1 := h518c.2.1
                                          have p518_2 := h518c.2.2.1
                                          have p518_3 := h518c.2.2.2
                                          rcases p518_3 (m.d 0 1) (by simp) with h537 | h537
                                          · linarith only [h1, h537, hlam]
                                          · linarith only [h468, h537, hlam]
                                        · have p518_0 := h518c.1
                                          have p518_1 := h518c.2.1
                                          have p518_2 := h518c.2.2.1
                                          have p518_3 := h518c.2.2.2
                                          linarith only [h467, hlam, p518_0]
                                        · have p518_0 := h518c.1
                                          have p518_1 := h518c.2.1
                                          have p518_2 := h518c.2.2.1
                                          have p518_3 := h518c.2.2.2
                                          linarith only [h1, h468, h511, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p518_1, u0elo2]
                                        · have p518_0 := h518c.1
                                          have p518_1 := h518c.2.1
                                          have p518_2 := h518c.2.2.1
                                          have p518_3 := h518c.2.2.2
                                          linarith only [h509, hlam, p518_0]
                                        · have p518_0 := h518c.1
                                          have p518_1 := h518c.2.1
                                          have p518_2 := h518c.2.2.1
                                          have p518_3 := h518c.2.2.2
                                          linarith only [hlam, p518_0]
                                        · have p518_0 := h518c.1
                                          have p518_1 := h518c.2.1
                                          have p518_2 := h518c.2.2.1
                                          have p518_3 := h518c.2.2.2
                                          linarith only [h511, hlam, p518_1]
                                        · have p518_0 := h518c.1
                                          have p518_1 := h518c.2.1
                                          have p518_2 := h518c.2.2.1
                                          have p518_3 := h518c.2.2.2
                                          linarith only [h468, hlam, p518_0]
                                        · have p518_0 := h518c.1
                                          have p518_1 := h518c.2.1
                                          have p518_2 := h518c.2.2.1
                                          have p518_3 := h518c.2.2.2
                                          linarith only [h1, h468, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p518_1, u0elo2]
                                        · have p518_0 := h518c.1
                                          have p518_1 := h518c.2.1
                                          have p518_2 := h518c.2.2.1
                                          have p518_3 := h518c.2.2.2
                                          linarith only [h510, hlam, p518_0]
                                        · have p518_0 := h518c.1
                                          have p518_1 := h518c.2.1
                                          have p518_2 := h518c.2.2.1
                                          have p518_3 := h518c.2.2.2
                                          linarith only [h1, h468, hc14, hlam, hphi, ht0b, ht45, ht5b, p518_1, u0elo2]
                                        · have p518_0 := h518c.1
                                          have p518_1 := h518c.2.1
                                          have p518_2 := h518c.2.2.1
                                          have p518_3 := h518c.2.2.2
                                          linarith only [hlam, p518_0]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h550 | h550
                                      · linarith only [h0, h471, h515, h550, hc12, hc34, hlam, hphi, ht23]
                                      · rcases h1bigk with h552c | h552c | h552c | h552c | h552c | h552c | h552c | h552c | h552c | h552c | h552c | h552c | h552c | h552c | h552c | h552c | h552c | h552c | h552c | h552c | h552c | h552c | h552c | h552c | h552c
                                        · have p552_0 := h552c.1
                                          have p552_1 := h552c.2.1
                                          have p552_2 := h552c.2.2.1
                                          have p552_3 := h552c.2.2.2
                                          linarith only [hlam, p552_0]
                                        · have p552_0 := h552c.1
                                          have p552_1 := h552c.2.1
                                          have p552_2 := h552c.2.2.1
                                          have p552_3 := h552c.2.2.2
                                          linarith only [h1, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p552_1, u0elo2]
                                        · have p552_0 := h552c.1
                                          have p552_1 := h552c.2.1
                                          have p552_2 := h552c.2.2.1
                                          have p552_3 := h552c.2.2.2
                                          linarith only [h1, hlam, p552_0]
                                        · have p552_0 := h552c.1
                                          have p552_1 := h552c.2.1
                                          have p552_2 := h552c.2.2.1
                                          have p552_3 := h552c.2.2.2
                                          linarith only [h1, hc14, hlam, hphi, ht0b, ht45, ht5b, p552_1, u0elo2]
                                        · have p552_0 := h552c.1
                                          have p552_1 := h552c.2.1
                                          have p552_2 := h552c.2.2.1
                                          have p552_3 := h552c.2.2.2
                                          linarith only [h1, hc15, hlam, hphi, ht0b, ht5b, p552_1, u0elo2]
                                        · have p552_0 := h552c.1
                                          have p552_1 := h552c.2.1
                                          have p552_2 := h552c.2.2.1
                                          have p552_3 := h552c.2.2.2
                                          linarith only [h0, hlam, p552_0]
                                        · have p552_0 := h552c.1
                                          have p552_1 := h552c.2.1
                                          have p552_2 := h552c.2.2.1
                                          have p552_3 := h552c.2.2.2
                                          linarith only [hlam, p552_0]
                                        · have p552_0 := h552c.1
                                          have p552_1 := h552c.2.1
                                          have p552_2 := h552c.2.2.1
                                          have p552_3 := h552c.2.2.2
                                          linarith only [h503, hlam, p552_0]
                                        · have p552_0 := h552c.1
                                          have p552_1 := h552c.2.1
                                          have p552_2 := h552c.2.2.1
                                          have p552_3 := h552c.2.2.2
                                          linarith only [h505, hlam, p552_0]
                                        · have p552_0 := h552c.1
                                          have p552_1 := h552c.2.1
                                          have p552_2 := h552c.2.2.1
                                          have p552_3 := h552c.2.2.2
                                          linarith only [h507, hlam, p552_0]
                                        · have p552_0 := h552c.1
                                          have p552_1 := h552c.2.1
                                          have p552_2 := h552c.2.2.1
                                          have p552_3 := h552c.2.2.2
                                          linarith only [h0, h503, hc12, hc23, hlam, hphi, p552_1]
                                        · have p552_0 := h552c.1
                                          have p552_1 := h552c.2.1
                                          have p552_2 := h552c.2.2.1
                                          have p552_3 := h552c.2.2.2
                                          rcases p552_3 (m.d 0 1) (by simp) with h564 | h564
                                          · linarith only [h1, h564, hlam]
                                          · linarith only [h0, h564, hlam]
                                        · have p552_0 := h552c.1
                                          have p552_1 := h552c.2.1
                                          have p552_2 := h552c.2.2.1
                                          have p552_3 := h552c.2.2.2
                                          linarith only [hlam, p552_0]
                                        · have p552_0 := h552c.1
                                          have p552_1 := h552c.2.1
                                          have p552_2 := h552c.2.2.1
                                          have p552_3 := h552c.2.2.2
                                          rcases p552_3 (m.d 0 1) (by simp) with h568 | h568
                                          · linarith only [h1, h568, hlam]
                                          · linarith only [h467, h568, hlam]
                                        · have p552_0 := h552c.1
                                          have p552_1 := h552c.2.1
                                          have p552_2 := h552c.2.2.1
                                          have p552_3 := h552c.2.2.2
                                          rcases p552_3 (m.d 0 1) (by simp) with h571 | h571
                                          · linarith only [h1, h571, hlam]
                                          · linarith only [h468, h571, hlam]
                                        · have p552_0 := h552c.1
                                          have p552_1 := h552c.2.1
                                          have p552_2 := h552c.2.2.1
                                          have p552_3 := h552c.2.2.2
                                          linarith only [h467, hlam, p552_0]
                                        · have p552_0 := h552c.1
                                          have p552_1 := h552c.2.1
                                          have p552_2 := h552c.2.2.1
                                          have p552_3 := h552c.2.2.2
                                          linarith only [h468, h511, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p552_1, u0elo0]
                                        · have p552_0 := h552c.1
                                          have p552_1 := h552c.2.1
                                          have p552_2 := h552c.2.2.1
                                          have p552_3 := h552c.2.2.2
                                          linarith only [h509, hlam, p552_0]
                                        · have p552_0 := h552c.1
                                          have p552_1 := h552c.2.1
                                          have p552_2 := h552c.2.2.1
                                          have p552_3 := h552c.2.2.2
                                          linarith only [hlam, p552_0]
                                        · have p552_0 := h552c.1
                                          have p552_1 := h552c.2.1
                                          have p552_2 := h552c.2.2.1
                                          have p552_3 := h552c.2.2.2
                                          linarith only [h511, hlam, p552_1]
                                        · have p552_0 := h552c.1
                                          have p552_1 := h552c.2.1
                                          have p552_2 := h552c.2.2.1
                                          have p552_3 := h552c.2.2.2
                                          linarith only [h468, hlam, p552_0]
                                        · have p552_0 := h552c.1
                                          have p552_1 := h552c.2.1
                                          have p552_2 := h552c.2.2.1
                                          have p552_3 := h552c.2.2.2
                                          linarith only [h1, h468, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p552_1, u0elo2]
                                        · have p552_0 := h552c.1
                                          have p552_1 := h552c.2.1
                                          have p552_2 := h552c.2.2.1
                                          have p552_3 := h552c.2.2.2
                                          linarith only [h510, hlam, p552_0]
                                        · have p552_0 := h552c.1
                                          have p552_1 := h552c.2.1
                                          have p552_2 := h552c.2.2.1
                                          have p552_3 := h552c.2.2.2
                                          linarith only [h1, h468, hc14, hlam, hphi, ht0b, ht45, ht5b, p552_1, u0elo2]
                                        · have p552_0 := h552c.1
                                          have p552_1 := h552c.2.1
                                          have p552_2 := h552c.2.2.1
                                          have p552_3 := h552c.2.2.2
                                          linarith only [hlam, p552_0]
                                  · linarith only [h0, h1, h503, h514, hc12, hc35, hlam, hphi, ht23]
                                · linarith only [h1, h468, h503, h505, h511, h513, hc12, hc34, hlam, hphi, ht23]
                            · linarith only [h0, h1, h510, hc12, hc35, hlam, hphi, ht23]
                          · linarith only [h1, h467, h505, h509, hc12, hc34, hlam, hphi, ht23]
                · linarith only [h1, h468, h488, hlam]
              · linarith only [h1, h467, h487, hlam]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h590 | h590
          · linarith only [h0, h1, h590, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h592 | h592
            · rcases m.htr 0 3 4 (by decide) (by decide) with h593 | h593
              · rcases m.htr 0 3 5 (by decide) (by decide) with h594 | h594
                · rcases m.htr 0 4 5 (by decide) (by decide) with h595 | h595
                  · linarith only [h0, h468, h592, h595, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h597 | h597
                    · linarith only [h0, h590, h597, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h599 | h599
                      · linarith only [h0, h468, h594, h599, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                      · linarith only [h592, h599, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h602 | h602
                  · linarith only [h0, h1, h592, h594, h602, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h604 | h604
                    · linarith only [h0, h1, h590, h594, h604, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo4]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h606 | h606
                      · linarith only [h0, h1, h594, h606, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo4]
                      · linarith only [h592, h606, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo1]
              · linarith only [h1, h467, h593, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h610 | h610
              · rcases m.htr 0 3 5 (by decide) (by decide) with h611 | h611
                · rcases m.htr 0 4 5 (by decide) (by decide) with h612 | h612
                  · linarith only [h467, h468, h612, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h614 | h614
                    · linarith only [h0, h468, h590, h611, h614, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h616 | h616
                      · linarith only [h0, h468, h592, h611, h616, hc04, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h618 | h618
                        · linarith only [h467, h468, h611, h616, h618, hc25, hlam, hphi, ht0b, ht5b, u0elo2]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h620 | h620
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h621 | h621
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h622 | h622
                              · linarith only [h467, h468, h592, h611, h612, h622, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h624 | h624
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h625 | h625
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h626 | h626
                                    · linarith only [h0, h468, h622, h626, hc12, hc24, hlam, hphi]
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h628 | h628
                                      · linarith only [h467, h468, h611, h620, h626, h628, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                                      · rcases h1bigk with h630c | h630c | h630c | h630c | h630c | h630c | h630c | h630c | h630c | h630c | h630c | h630c | h630c | h630c | h630c | h630c | h630c | h630c | h630c | h630c | h630c | h630c | h630c | h630c | h630c
                                        · have p630_0 := h630c.1
                                          have p630_1 := h630c.2.1
                                          have p630_2 := h630c.2.2.1
                                          have p630_3 := h630c.2.2.2
                                          linarith only [hlam, p630_0]
                                        · have p630_0 := h630c.1
                                          have p630_1 := h630c.2.1
                                          have p630_2 := h630c.2.2.1
                                          have p630_3 := h630c.2.2.2
                                          linarith only [h468, h611, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p630_1, u0elo2]
                                        · have p630_0 := h630c.1
                                          have p630_1 := h630c.2.1
                                          have p630_2 := h630c.2.2.1
                                          have p630_3 := h630c.2.2.2
                                          linarith only [h1, hlam, p630_0]
                                        · have p630_0 := h630c.1
                                          have p630_1 := h630c.2.1
                                          have p630_2 := h630c.2.2.1
                                          have p630_3 := h630c.2.2.2
                                          linarith only [h468, h611, hc14, hlam, hphi, ht0b, ht45, ht5b, p630_1, u0elo2]
                                        · have p630_0 := h630c.1
                                          have p630_1 := h630c.2.1
                                          have p630_2 := h630c.2.2.1
                                          have p630_3 := h630c.2.2.2
                                          linarith only [h468, hlam, p630_0]
                                        · have p630_0 := h630c.1
                                          have p630_1 := h630c.2.1
                                          have p630_2 := h630c.2.2.1
                                          have p630_3 := h630c.2.2.2
                                          linarith only [h0, hlam, p630_0]
                                        · have p630_0 := h630c.1
                                          have p630_1 := h630c.2.1
                                          have p630_2 := h630c.2.2.1
                                          have p630_3 := h630c.2.2.2
                                          linarith only [hlam, p630_0]
                                        · have p630_0 := h630c.1
                                          have p630_1 := h630c.2.1
                                          have p630_2 := h630c.2.2.1
                                          have p630_3 := h630c.2.2.2
                                          linarith only [h614, hlam, p630_0]
                                        · have p630_0 := h630c.1
                                          have p630_1 := h630c.2.1
                                          have p630_2 := h630c.2.2.1
                                          have p630_3 := h630c.2.2.2
                                          linarith only [h616, hlam, p630_0]
                                        · have p630_0 := h630c.1
                                          have p630_1 := h630c.2.1
                                          have p630_2 := h630c.2.2.1
                                          have p630_3 := h630c.2.2.2
                                          linarith only [h618, hlam, p630_0]
                                        · have p630_0 := h630c.1
                                          have p630_1 := h630c.2.1
                                          have p630_2 := h630c.2.2.1
                                          have p630_3 := h630c.2.2.2
                                          linarith only [h0, h614, hc12, hc23, hlam, hphi, p630_1]
                                        · have p630_0 := h630c.1
                                          have p630_1 := h630c.2.1
                                          have p630_2 := h630c.2.2.1
                                          have p630_3 := h630c.2.2.2
                                          rcases p630_3 (m.d 0 1) (by simp) with h642 | h642
                                          · linarith only [h1, h642, hlam]
                                          · linarith only [h0, h642, hlam]
                                        · have p630_0 := h630c.1
                                          have p630_1 := h630c.2.1
                                          have p630_2 := h630c.2.2.1
                                          have p630_3 := h630c.2.2.2
                                          linarith only [hlam, p630_0]
                                        · have p630_0 := h630c.1
                                          have p630_1 := h630c.2.1
                                          have p630_2 := h630c.2.2.1
                                          have p630_3 := h630c.2.2.2
                                          rcases p630_3 (m.d 0 1) (by simp) with h646 | h646
                                          · linarith only [h1, h646, hlam]
                                          · linarith only [h467, h646, hlam]
                                        · have p630_0 := h630c.1
                                          have p630_1 := h630c.2.1
                                          have p630_2 := h630c.2.2.1
                                          have p630_3 := h630c.2.2.2
                                          linarith only [h467, h468, h614, h616, hc12, hc23, hlam, hphi, p630_1]
                                        · have p630_0 := h630c.1
                                          have p630_1 := h630c.2.1
                                          have p630_2 := h630c.2.2.1
                                          have p630_3 := h630c.2.2.2
                                          linarith only [h467, hlam, p630_0]
                                        · have p630_0 := h630c.1
                                          have p630_1 := h630c.2.1
                                          have p630_2 := h630c.2.2.1
                                          have p630_3 := h630c.2.2.2
                                          linarith only [h467, h468, h611, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p630_1, u0elo2]
                                        · have p630_0 := h630c.1
                                          have p630_1 := h630c.2.1
                                          have p630_2 := h630c.2.2.1
                                          have p630_3 := h630c.2.2.2
                                          linarith only [h620, hlam, p630_0]
                                        · have p630_0 := h630c.1
                                          have p630_1 := h630c.2.1
                                          have p630_2 := h630c.2.2.1
                                          have p630_3 := h630c.2.2.2
                                          linarith only [hlam, p630_0]
                                        · have p630_0 := h630c.1
                                          have p630_1 := h630c.2.1
                                          have p630_2 := h630c.2.2.1
                                          have p630_3 := h630c.2.2.2
                                          linarith only [h622, hlam, p630_1]
                                        · have p630_0 := h630c.1
                                          have p630_1 := h630c.2.1
                                          have p630_2 := h630c.2.2.1
                                          have p630_3 := h630c.2.2.2
                                          linarith only [h467, h618, h626, hc14, hc45, hlam, hphi, p630_1]
                                        · have p630_0 := h630c.1
                                          have p630_1 := h630c.2.1
                                          have p630_2 := h630c.2.2.1
                                          have p630_3 := h630c.2.2.2
                                          rcases p630_3 (m.d 0 1) (by simp) with h656 | h656
                                          · linarith only [h468, h656, hlam]
                                          · linarith only [h0, h656, hlam]
                                        · have p630_0 := h630c.1
                                          have p630_1 := h630c.2.1
                                          have p630_2 := h630c.2.2.1
                                          have p630_3 := h630c.2.2.2
                                          linarith only [h621, hlam, p630_0]
                                        · have p630_0 := h630c.1
                                          have p630_1 := h630c.2.1
                                          have p630_2 := h630c.2.2.1
                                          have p630_3 := h630c.2.2.2
                                          rcases p630_3 (m.d 0 1) (by simp) with h660 | h660
                                          · linarith only [h468, h660, hlam]
                                          · linarith only [h467, h660, hlam]
                                        · have p630_0 := h630c.1
                                          have p630_1 := h630c.2.1
                                          have p630_2 := h630c.2.2.1
                                          have p630_3 := h630c.2.2.2
                                          linarith only [hlam, p630_0]
                                  · linarith only [h611, h614, h625, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                                · linarith only [h467, h468, h614, h616, h621, h624, hc12, hc34, hlam, hphi, ht23]
                            · linarith only [h611, h621, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                          · linarith only [h1, h467, h616, h620, hc12, hc34, hlam, hphi, ht23]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h668 | h668
                  · linarith only [h1, h467, h611, h668, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h670 | h670
                    · linarith only [h0, h1, h611, h670, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo4]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h672 | h672
                      · linarith only [h0, h1, h592, h611, h672, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo4]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h674 | h674
                        · linarith only [h0, h1, h611, h674, hc25, hlam, hphi, ht0b, ht5b, u0elo4]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h676 | h676
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h677 | h677
                            · linarith only [h1, h467, h611, h670, h672, h677, hc12, hc23, hlam, hphi]
                            · linarith only [h1, h467, h672, h677, hc12, hc35, hlam, hphi, ht23]
                          · linarith only [h1, h467, h672, h676, hc12, hc34, hlam, hphi, ht23]
              · linarith only [h1, h467, h610, hlam]
      · rcases m.htr 0 1 5 (by decide) (by decide) with h682 | h682
        · rcases m.htr 0 2 3 (by decide) (by decide) with h683 | h683
          · linarith only [h0, h1, h683, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h685 | h685
            · linarith only [h0, h467, h685, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h687 | h687
              · rcases m.htr 0 3 5 (by decide) (by decide) with h688 | h688
                · rcases m.htr 0 4 5 (by decide) (by decide) with h689 | h689
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h690 | h690
                    · linarith only [h0, h683, h690, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h692 | h692
                      · linarith only [h0, h467, h682, h685, h692, hc15, hlam, hphi, ht0b, ht5b, u0elo1]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h694 | h694
                        · linarith only [h0, h694, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h696 | h696
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h697 | h697
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h698 | h698
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h699 | h699
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h700 | h700
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h701 | h701
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h702 | h702
                                      · linarith only [h687, h702, hc45, hlam, hphi, ht0b, ht5b, u0elo2]
                                      · linarith only [h687, h689, h702, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                                    · linarith only [h467, h682, h692, h698, h701, hlam]
                                  · linarith only [h467, h682, h690, h696, h697, h700, hlam]
                                · linarith only [h467, h682, h690, h694, h696, h699, hc12, hc34, hlam, hphi, ht23]
                              · linarith only [h467, h682, h694, h698, hc12, hc45, hlam, hphi, ht23, ht34]
                            · linarith only [h467, h682, h694, h696, h697, hc12, hc35, hlam, hphi, ht23]
                          · linarith only [h687, h696, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                  · linarith only [h467, h682, h689, hlam]
                · linarith only [h467, h682, h687, h688, hlam]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h713 | h713
                · rcases m.htr 0 4 5 (by decide) (by decide) with h714 | h714
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h715 | h715
                    · linarith only [h0, h683, h715, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h717 | h717
                      · linarith only [h0, h1, h682, h685, h687, h717, hc15, hlam, hphi, ht0b, ht5b, u0elo1]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h719 | h719
                        · linarith only [h0, h719, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h721 | h721
                          · linarith only [h1, h682, h687, h715, h719, h721, hc12, hc23, hlam, hphi]
                          · linarith only [h1, h682, h719, h721, hc12, hc34, hlam, hphi, ht23]
                  · linarith only [h1, h682, h687, h714, hlam]
                · linarith only [h1, h682, h713, hlam]
        · rcases m.htr 0 2 3 (by decide) (by decide) with h726 | h726
          · linarith only [h0, h1, h726, hlam]
          · rcases m.htr 0 2 4 (by decide) (by decide) with h728 | h728
            · linarith only [h0, h467, h728, hlam]
            · rcases m.htr 0 3 4 (by decide) (by decide) with h730 | h730
              · rcases m.htr 0 3 5 (by decide) (by decide) with h731 | h731
                · rcases m.htr 0 4 5 (by decide) (by decide) with h732 | h732
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h733 | h733
                    · linarith only [h0, h682, h726, h730, h732, h733, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h735 | h735
                      · linarith only [h0, h728, h732, h735, hc45, hlam, hphi, ht0b, ht5b, u0elo1]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h737 | h737
                        · linarith only [h0, h737, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h739 | h739
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h740 | h740
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h741 | h741
                              · rcases m.htr 2 3 4 (by decide) (by decide) with h742 | h742
                                · rcases m.htr 2 3 5 (by decide) (by decide) with h743 | h743
                                  · rcases m.htr 2 4 5 (by decide) (by decide) with h744 | h744
                                    · rcases m.htr 3 4 5 (by decide) (by decide) with h745 | h745
                                      · linarith only [h730, h745, hc45, hlam, hphi, ht0b, ht5b, u0elo2]
                                      · linarith only [h730, h732, h745, hc34, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                                    · linarith only [h0, h682, h730, h732, h735, h741, h744, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                                  · linarith only [h0, h682, h731, h733, h739, h741, h743, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                                · linarith only [h0, h682, h733, h739, h741, h742, hc12, hc34, hlam, hphi, ht23]
                              · linarith only [h730, h732, h741, hc14, hlam, hphi, ht0b, ht45, ht5b, u0elo2]
                            · linarith only [h0, h467, h731, h739, h740, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo2]
                          · linarith only [h730, h739, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h754 | h754
                    · linarith only [h0, h726, h754, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h756 | h756
                      · linarith only [h0, h467, h728, h756, hlam]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h758 | h758
                        · linarith only [h0, h758, hc25, hlam, hphi, ht0b, ht5b, u0elo0]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h760 | h760
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h761 | h761
                            · rcases m.htr 1 4 5 (by decide) (by decide) with h762 | h762
                              · linarith only [h0, h467, h732, h754, h760, h762, hc12, hc23, hlam, hphi]
                              · linarith only [h0, h467, h762, hc12, hc45, hlam, hphi, ht23, ht34]
                            · linarith only [h731, h761, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo2]
                          · linarith only [h0, h1, h760, hc12, hc34, hlam, hphi, ht23]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h767 | h767
                  · linarith only [h730, h731, h767, hlam]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h769 | h769
                    · linarith only [h0, h769, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h771 | h771
                      · linarith only [h0, h467, h730, h731, h771, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo4]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h773 | h773
                        · linarith only [h0, h467, h730, h731, h773, hc25, hlam, hphi, ht0b, ht5b, u0elo4]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h775 | h775
                          · rcases m.htr 1 3 5 (by decide) (by decide) with h776 | h776
                            · linarith only [h0, h467, h730, h731, h769, h776, hc12, hc23, hlam, hphi]
                            · linarith only [h0, h1, h776, hc12, hc35, hlam, hphi, ht23]
                          · linarith only [h0, h1, h730, h731, h775, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u0elo4]
              · rcases m.htr 0 3 5 (by decide) (by decide) with h780 | h780
                · rcases m.htr 0 4 5 (by decide) (by decide) with h781 | h781
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h782 | h782
                    · linarith only [h0, h782, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h784 | h784
                      · linarith only [h0, h682, h730, h780, h784, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h786 | h786
                        · linarith only [h0, h682, h730, h780, h786, hc25, hlam, hphi, ht0b, ht5b, u0elo3]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h788 | h788
                          · linarith only [h0, h682, h730, h780, h782, h788, hc12, hc23, hlam, hphi]
                          · linarith only [h0, h1, h788, hc12, hc34, hlam, hphi, ht23]
                  · linarith only [h730, h780, h781, hlam]
                · rcases m.htr 0 4 5 (by decide) (by decide) with h792 | h792
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h793 | h793
                    · linarith only [h0, h793, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h795 | h795
                      · linarith only [h0, h1, h780, h792, h795, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo3]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h797 | h797
                        · linarith only [h0, h1, h780, h792, h797, hc25, hlam, hphi, ht0b, ht5b, u0elo3]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h799 | h799
                          · linarith only [h0, h1, h730, h793, h799, hc12, hc23, hlam, hphi]
                          · linarith only [h0, h1, h799, hc12, hc34, hlam, hphi, ht23]
                  · rcases m.htr 1 2 3 (by decide) (by decide) with h802 | h802
                    · linarith only [h0, h802, hc23, hlam, hphi, ht0b, ht34, ht45, ht5b, u0elo0]
                    · rcases m.htr 1 2 4 (by decide) (by decide) with h804 | h804
                      · linarith only [h0, h1, h730, h792, h804, hc24, hlam, hphi, ht0b, ht45, ht5b, u0elo4]
                      · rcases m.htr 1 2 5 (by decide) (by decide) with h806 | h806
                        · linarith only [h0, h1, h730, h792, h806, hc25, hlam, hphi, ht0b, ht5b, u0elo4]
                        · rcases m.htr 1 3 4 (by decide) (by decide) with h808 | h808
                          · linarith only [h0, h1, h730, h802, h808, hc12, hc23, hlam, hphi]
                          · linarith only [h0, h1, h808, hc12, hc34, hlam, hphi, ht23]
  · exact r1l7_20_11_13_14_H_L_L_I_L_I_L_I_s0 m hb0 hb1 hb3 hb4 h0

end R2N4
