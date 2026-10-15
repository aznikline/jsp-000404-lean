import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


set_option maxHeartbeats 4664000 in
theorem r1l7_10_12_13_25_L_I_L_R_L_R_H_I_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
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
  have h0emax := hb0.2.2
  have h2ehi := hb2.1
  have h3ehi := hb3.1
  have h5bigk := hb5.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
  · rcases m.htr 0 1 5 (by decide) (by decide) with h2 | h2
    · rcases m.htr 0 2 3 (by decide) (by decide) with h3 | h3
      · rcases m.htr 0 2 5 (by decide) (by decide) with h4 | h4
        · rcases m.htr 0 3 4 (by decide) (by decide) with h5 | h5
          · rcases m.htr 0 3 5 (by decide) (by decide) with h6 | h6
            · rcases m.htr 0 4 5 (by decide) (by decide) with h7 | h7
              · rcases m.htr 1 2 3 (by decide) (by decide) with h8 | h8
                · rcases m.htr 1 2 4 (by decide) (by decide) with h9 | h9
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h10 | h10
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h11 | h11
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h12 | h12
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h13 | h13
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h14 | h14
                            · linarith only [h0, h14, h8, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                            · linarith only [h0, h11, h14, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h17 | h17
                            · linarith only [h0, h17, h8, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                            · linarith only [h0, h11, h17, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                        · linarith only [h0, h11, h12, h3, h6, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h21 | h21
                        · linarith only [h11, h21, hc34, hlam, hphi, u3ehi4]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h23 | h23
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h24 | h24
                            · linarith only [h0, h11, h24, h3, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h26 | h26
                              · linarith only [h21, h26, h8, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h28 | h28
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h29 | h29
                                  · rcases h0emax with h30 | h30 | h30 | h30 | h30
                                    · linarith only [h0, h30, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                                    · linarith only [h21, h29, h3, h30, h5, h8, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                                    · linarith only [h21, h29, h30, h5, h8, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                                    · linarith only [h21, h29, h30, h5, h8, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                                    · linarith only [h21, h30, h6, h8, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                                  · linarith only [h28, h29, h9, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                                · linarith only [h0, h23, h28, h9, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h38 | h38
                            · linarith only [h11, h23, h3, h38, h5, h7, h8, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h40 | h40
                              · linarith only [h21, h40, h8, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h42 | h42
                                · linarith only [h11, h23, h42, h8, hc24, hlam, hphi, u2ehi2]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h44 | h44
                                  · linarith only [h11, h23, h44, h8, hc34, hlam, hphi, ht23, u2ehi2]
                                  · linarith only [h0, h11, h3, h44, h5, h7, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                    · linarith only [h0, h10, h4, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                  · linarith only [h8, h9, hc24, hlam, hphi, u2ehi2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h49 | h49
                  · linarith only [h49, h8, hc23, hlam, hphi, u2ehi3]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h51 | h51
                    · linarith only [h0, h3, h51, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi4]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h53 | h53
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h54 | h54
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h55 | h55
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h56 | h56
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h57 | h57
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h58 | h58
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h59 | h59
                                  · rcases h0emax with h60 | h60 | h60 | h60 | h60
                                    · linarith only [h0, h3, h51, h56, h58, h60, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                                    · linarith only [h3, h51, h56, h58, h60, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                                    · linarith only [h1, h53, h59, h60, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi4]
                                    · linarith only [h4, h51, h60, h7, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                                    · linarith only [h4, h51, h60, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                                  · linarith only [h0, h3, h49, h55, h56, h59, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                                · linarith only [h49, h55, h58, hlam]
                              · linarith only [h0, h3, h57, h6, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                            · linarith only [h53, h56, h8, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h70 | h70
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h71 | h71
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h72 | h72
                                · linarith only [h49, h55, h72, hc24, hlam, hphi, u2ehi1]
                                · linarith only [h49, h72, hc45, hlam, hphi, ht23, ht34, u2ehi1]
                              · linarith only [h0, h3, h6, h71, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                            · linarith only [h54, h70, h8, hc34, hlam, hphi, u3ehi4]
                        · linarith only [h53, h54, hc35, hlam, hphi, u3ehi3]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h78 | h78
                        · linarith only [h0, h3, h5, h53, h78, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi4]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h80 | h80
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h81 | h81
                            · linarith only [h0, h3, h53, h81, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                            · linarith only [h5, h8, h81, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h84 | h84
                            · linarith only [h0, h3, h53, h8, h84, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                            · linarith only [h0, h3, h5, h8, h84, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h87 | h87
                · rcases m.htr 1 2 4 (by decide) (by decide) with h88 | h88
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h89 | h89
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h90 | h90
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h91 | h91
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h92 | h92
                          · linarith only [h0, h5, h7, h88, h92, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h94 | h94
                            · linarith only [h0, h87, h94, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                            · linarith only [h1, h90, h94, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                        · linarith only [h90, h91, hc35, hlam, hphi, u3ehi3]
                      · linarith only [h5, h7, h90, hc45, hlam, hphi, ht34, u3ehi1]
                    · linarith only [h0, h4, h87, h89, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                  · linarith only [h87, h88, hc24, hlam, hphi, u2ehi2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h101 | h101
                  · linarith only [h101, h87, hc23, hlam, hphi, u2ehi3]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h103 | h103
                    · linarith only [h0, h103, h3, h87, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi4]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h105 | h105
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h106 | h106
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h107 | h107
                          · linarith only [h101, h103, h107, h4, h7, hc24, hlam, hphi, u2ehi1]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h109 | h109
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h110 | h110
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h111 | h111
                                · linarith only [h0, h109, h111, h3, h5, h7, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                                · linarith only [h101, h111, hc45, hlam, hphi, ht23, ht34, u2ehi1]
                              · linarith only [h1, h106, h110, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                            · linarith only [h106, h109, h87, hc34, hlam, hphi, u3ehi4]
                        · linarith only [h105, h106, hc35, hlam, hphi, u3ehi3]
                      · linarith only [h105, h5, h7, hc45, hlam, hphi, ht34, u3ehi1]
            · linarith only [h5, h6, hc35, hlam, hphi, u3ehi3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h119 | h119
            · linarith only [h119, h5, hc34, hlam, hphi, u3ehi4]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h121 | h121
              · rcases m.htr 1 2 3 (by decide) (by decide) with h122 | h122
                · rcases m.htr 1 2 4 (by decide) (by decide) with h123 | h123
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h124 | h124
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h125 | h125
                      · linarith only [h1, h125, h5, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h127 | h127
                        · linarith only [h1, h119, h127, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h129 | h129
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h130 | h130
                            · linarith only [h1, h122, h130, h5, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h132 | h132
                              · linarith only [h1, h119, h122, h132, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h134 | h134
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h135 | h135
                                  · rcases h0emax with h136 | h136 | h136 | h136 | h136
                                    · linarith only [h0, h136, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                                    · linarith only [h0, h123, h132, h134, h136, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                                    · rcases h5bigk with h139c | h139c | h139c | h139c | h139c | h139c | h139c | h139c | h139c | h139c | h139c | h139c | h139c | h139c | h139c | h139c | h139c | h139c | h139c | h139c | h139c | h139c | h139c | h139c | h139c
                                      · have p139_0 := h139c.1
                                        have p139_1 := h139c.2.1
                                        have p139_2 := h139c.2.2.1
                                        have p139_3 := h139c.2.2.2
                                        linarith only [hlam, p139_0]
                                      · have p139_0 := h139c.1
                                        have p139_1 := h139c.2.1
                                        have p139_2 := h139c.2.2.1
                                        have p139_3 := h139c.2.2.2
                                        linarith only [h121, h122, h127, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p139_1, u2ehi2]
                                      · have p139_0 := h139c.1
                                        have p139_1 := h139c.2.1
                                        have p139_2 := h139c.2.2.1
                                        have p139_3 := h139c.2.2.2
                                        linarith only [h0, h132, h4, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p139_1, u2ehi2]
                                      · have p139_0 := h139c.1
                                        have p139_1 := h139c.2.1
                                        have p139_2 := h139c.2.2.1
                                        have p139_3 := h139c.2.2.2
                                        linarith only [h119, hlam, p139_1]
                                      · have p139_0 := h139c.1
                                        have p139_1 := h139c.2.1
                                        have p139_2 := h139c.2.2.1
                                        have p139_3 := h139c.2.2.2
                                        rcases p139_3 (m.d 0 5) (by simp) with h144 | h144
                                        · rcases p139_3 (m.d 1 5) (by simp) with h145 | h145
                                          · linarith only [h145, h2, hlam]
                                          · linarith only [h129, h145, hlam]
                                        · linarith only [h121, h144, hlam]
                                      · have p139_0 := h139c.1
                                        have p139_1 := h139c.2.1
                                        have p139_2 := h139c.2.2.1
                                        have p139_3 := h139c.2.2.2
                                        linarith only [h2, hlam, p139_0]
                                      · have p139_0 := h139c.1
                                        have p139_1 := h139c.2.1
                                        have p139_2 := h139c.2.2.1
                                        have p139_3 := h139c.2.2.2
                                        linarith only [hlam, p139_0]
                                      · have p139_0 := h139c.1
                                        have p139_1 := h139c.2.1
                                        have p139_2 := h139c.2.2.1
                                        have p139_3 := h139c.2.2.2
                                        linarith only [h129, h132, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p139_1, u2ehi2]
                                      · have p139_0 := h139c.1
                                        have p139_1 := h139c.2.1
                                        have p139_2 := h139c.2.2.1
                                        have p139_3 := h139c.2.2.2
                                        linarith only [h127, hlam, p139_1]
                                      · have p139_0 := h139c.1
                                        have p139_1 := h139c.2.1
                                        have p139_2 := h139c.2.2.1
                                        have p139_3 := h139c.2.2.2
                                        linarith only [h0, h123, h129, hc01, hc45, hlam, hphi, ht0b, ht5b, p139_1]
                                      · have p139_0 := h139c.1
                                        have p139_1 := h139c.2.1
                                        have p139_2 := h139c.2.2.1
                                        have p139_3 := h139c.2.2.2
                                        linarith only [h4, hlam, p139_1]
                                      · have p139_0 := h139c.1
                                        have p139_1 := h139c.2.1
                                        have p139_2 := h139c.2.2.1
                                        have p139_3 := h139c.2.2.2
                                        linarith only [h124, hlam, p139_1]
                                      · have p139_0 := h139c.1
                                        have p139_1 := h139c.2.1
                                        have p139_2 := h139c.2.2.1
                                        have p139_3 := h139c.2.2.2
                                        linarith only [hlam, p139_0]
                                      · have p139_0 := h139c.1
                                        have p139_1 := h139c.2.1
                                        have p139_2 := h139c.2.2.1
                                        have p139_3 := h139c.2.2.2
                                        linarith only [h132, hlam, p139_1]
                                      · have p139_0 := h139c.1
                                        have p139_1 := h139c.2.1
                                        have p139_2 := h139c.2.2.1
                                        have p139_3 := h139c.2.2.2
                                        linarith only [h0, h4, hc01, hc45, hlam, hphi, ht0b, ht5b, p139_1]
                                      · have p139_0 := h139c.1
                                        have p139_1 := h139c.2.1
                                        have p139_2 := h139c.2.2.1
                                        have p139_3 := h139c.2.2.2
                                        linarith only [h135, h4, hc34, hlam, hphi, ht23, p139_1, u2ehi4]
                                      · have p139_0 := h139c.1
                                        have p139_1 := h139c.2.1
                                        have p139_2 := h139c.2.2.1
                                        have p139_3 := h139c.2.2.2
                                        linarith only [h124, h135, hc34, hlam, hphi, ht23, p139_1, u2ehi4]
                                      · have p139_0 := h139c.1
                                        have p139_1 := h139c.2.1
                                        have p139_2 := h139c.2.2.1
                                        have p139_3 := h139c.2.2.2
                                        linarith only [h135, hc34, hlam, hphi, ht23, p139_1, u2ehi4]
                                      · have p139_0 := h139c.1
                                        have p139_1 := h139c.2.1
                                        have p139_2 := h139c.2.2.1
                                        have p139_3 := h139c.2.2.2
                                        linarith only [hlam, p139_0]
                                      · have p139_0 := h139c.1
                                        have p139_1 := h139c.2.1
                                        have p139_2 := h139c.2.2.1
                                        have p139_3 := h139c.2.2.2
                                        rcases p139_3 (m.d 0 5) (by simp) with h163 | h163
                                        · linarith only [h119, h163, hlam]
                                        · linarith only [h121, h163, hlam]
                                      · have p139_0 := h139c.1
                                        have p139_1 := h139c.2.1
                                        have p139_2 := h139c.2.2.1
                                        have p139_3 := h139c.2.2.2
                                        linarith only [h121, hlam, p139_0]
                                      · have p139_0 := h139c.1
                                        have p139_1 := h139c.2.1
                                        have p139_2 := h139c.2.2.1
                                        have p139_3 := h139c.2.2.2
                                        linarith only [h129, hlam, p139_0]
                                      · have p139_0 := h139c.1
                                        have p139_1 := h139c.2.1
                                        have p139_2 := h139c.2.2.1
                                        have p139_3 := h139c.2.2.2
                                        linarith only [h134, hlam, p139_0]
                                      · have p139_0 := h139c.1
                                        have p139_1 := h139c.2.1
                                        have p139_2 := h139c.2.2.1
                                        have p139_3 := h139c.2.2.2
                                        linarith only [h135, hlam, p139_0]
                                      · have p139_0 := h139c.1
                                        have p139_1 := h139c.2.1
                                        have p139_2 := h139c.2.2.1
                                        have p139_3 := h139c.2.2.2
                                        linarith only [hlam, p139_0]
                                    · rcases h5bigk with h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c | h171c
                                      · have p171_0 := h171c.1
                                        have p171_1 := h171c.2.1
                                        have p171_2 := h171c.2.2.1
                                        have p171_3 := h171c.2.2.2
                                        linarith only [hlam, p171_0]
                                      · have p171_0 := h171c.1
                                        have p171_1 := h171c.2.1
                                        have p171_2 := h171c.2.2.1
                                        have p171_3 := h171c.2.2.2
                                        linarith only [h121, h122, h127, h136, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p171_1, u2ehi2]
                                      · have p171_0 := h171c.1
                                        have p171_1 := h171c.2.1
                                        have p171_2 := h171c.2.2.1
                                        have p171_3 := h171c.2.2.2
                                        linarith only [h121, h132, h136, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p171_1, u2ehi2]
                                      · have p171_0 := h171c.1
                                        have p171_1 := h171c.2.1
                                        have p171_2 := h171c.2.2.1
                                        have p171_3 := h171c.2.2.2
                                        linarith only [h119, hlam, p171_1]
                                      · have p171_0 := h171c.1
                                        have p171_1 := h171c.2.1
                                        have p171_2 := h171c.2.2.1
                                        have p171_3 := h171c.2.2.2
                                        linarith only [h121, h136, hc45, hlam, hphi, ht0b, ht5b, p171_1]
                                      · have p171_0 := h171c.1
                                        have p171_1 := h171c.2.1
                                        have p171_2 := h171c.2.2.1
                                        have p171_3 := h171c.2.2.2
                                        linarith only [h2, hlam, p171_0]
                                      · have p171_0 := h171c.1
                                        have p171_1 := h171c.2.1
                                        have p171_2 := h171c.2.2.1
                                        have p171_3 := h171c.2.2.2
                                        linarith only [hlam, p171_0]
                                      · have p171_0 := h171c.1
                                        have p171_1 := h171c.2.1
                                        have p171_2 := h171c.2.2.1
                                        have p171_3 := h171c.2.2.2
                                        linarith only [h132, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p171_1, u2ehi2]
                                      · have p171_0 := h171c.1
                                        have p171_1 := h171c.2.1
                                        have p171_2 := h171c.2.2.1
                                        have p171_3 := h171c.2.2.2
                                        linarith only [h127, hlam, p171_1]
                                      · have p171_0 := h171c.1
                                        have p171_1 := h171c.2.1
                                        have p171_2 := h171c.2.2.1
                                        have p171_3 := h171c.2.2.2
                                        linarith only [h121, h136, h2, hc45, hlam, hphi, ht0b, ht5b, p171_1]
                                      · have p171_0 := h171c.1
                                        have p171_1 := h171c.2.1
                                        have p171_2 := h171c.2.2.1
                                        have p171_3 := h171c.2.2.2
                                        linarith only [h4, hlam, p171_1]
                                      · have p171_0 := h171c.1
                                        have p171_1 := h171c.2.1
                                        have p171_2 := h171c.2.2.1
                                        have p171_3 := h171c.2.2.2
                                        linarith only [h124, hlam, p171_1]
                                      · have p171_0 := h171c.1
                                        have p171_1 := h171c.2.1
                                        have p171_2 := h171c.2.2.1
                                        have p171_3 := h171c.2.2.2
                                        linarith only [hlam, p171_0]
                                      · have p171_0 := h171c.1
                                        have p171_1 := h171c.2.1
                                        have p171_2 := h171c.2.2.1
                                        have p171_3 := h171c.2.2.2
                                        linarith only [h132, hlam, p171_1]
                                      · have p171_0 := h171c.1
                                        have p171_1 := h171c.2.1
                                        have p171_2 := h171c.2.2.1
                                        have p171_3 := h171c.2.2.2
                                        linarith only [h0, h4, hc01, hc45, hlam, hphi, ht0b, ht5b, p171_1]
                                      · have p171_0 := h171c.1
                                        have p171_1 := h171c.2.1
                                        have p171_2 := h171c.2.2.1
                                        have p171_3 := h171c.2.2.2
                                        linarith only [h119, h135, hc34, hlam, hphi, p171_1, u3ehi0]
                                      · have p171_0 := h171c.1
                                        have p171_1 := h171c.2.1
                                        have p171_2 := h171c.2.2.1
                                        have p171_3 := h171c.2.2.2
                                        linarith only [h124, h135, hc34, hlam, hphi, ht23, p171_1, u2ehi4]
                                      · have p171_0 := h171c.1
                                        have p171_1 := h171c.2.1
                                        have p171_2 := h171c.2.2.1
                                        have p171_3 := h171c.2.2.2
                                        linarith only [h135, hc34, hlam, hphi, ht23, p171_1, u2ehi4]
                                      · have p171_0 := h171c.1
                                        have p171_1 := h171c.2.1
                                        have p171_2 := h171c.2.2.1
                                        have p171_3 := h171c.2.2.2
                                        linarith only [hlam, p171_0]
                                      · have p171_0 := h171c.1
                                        have p171_1 := h171c.2.1
                                        have p171_2 := h171c.2.2.1
                                        have p171_3 := h171c.2.2.2
                                        rcases p171_3 (m.d 0 5) (by simp) with h191 | h191
                                        · linarith only [h119, h191, hlam]
                                        · linarith only [h121, h191, hlam]
                                      · have p171_0 := h171c.1
                                        have p171_1 := h171c.2.1
                                        have p171_2 := h171c.2.2.1
                                        have p171_3 := h171c.2.2.2
                                        linarith only [h121, hlam, p171_0]
                                      · have p171_0 := h171c.1
                                        have p171_1 := h171c.2.1
                                        have p171_2 := h171c.2.2.1
                                        have p171_3 := h171c.2.2.2
                                        linarith only [h129, hlam, p171_0]
                                      · have p171_0 := h171c.1
                                        have p171_1 := h171c.2.1
                                        have p171_2 := h171c.2.2.1
                                        have p171_3 := h171c.2.2.2
                                        linarith only [h134, hlam, p171_0]
                                      · have p171_0 := h171c.1
                                        have p171_1 := h171c.2.1
                                        have p171_2 := h171c.2.2.1
                                        have p171_3 := h171c.2.2.2
                                        linarith only [h135, hlam, p171_0]
                                      · have p171_0 := h171c.1
                                        have p171_1 := h171c.2.1
                                        have p171_2 := h171c.2.2.1
                                        have p171_3 := h171c.2.2.2
                                        linarith only [hlam, p171_0]
                                    · rcases h5bigk with h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c | h199c
                                      · have p199_0 := h199c.1
                                        have p199_1 := h199c.2.1
                                        have p199_2 := h199c.2.2.1
                                        have p199_3 := h199c.2.2.2
                                        linarith only [hlam, p199_0]
                                      · have p199_0 := h199c.1
                                        have p199_1 := h199c.2.1
                                        have p199_2 := h199c.2.2.1
                                        have p199_3 := h199c.2.2.2
                                        linarith only [h121, h122, h127, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p199_1, u2ehi2]
                                      · have p199_0 := h199c.1
                                        have p199_1 := h199c.2.1
                                        have p199_2 := h199c.2.2.1
                                        have p199_3 := h199c.2.2.2
                                        linarith only [h0, h132, h4, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p199_1, u2ehi2]
                                      · have p199_0 := h199c.1
                                        have p199_1 := h199c.2.1
                                        have p199_2 := h199c.2.2.1
                                        have p199_3 := h199c.2.2.2
                                        linarith only [h119, hlam, p199_1]
                                      · have p199_0 := h199c.1
                                        have p199_1 := h199c.2.1
                                        have p199_2 := h199c.2.2.1
                                        have p199_3 := h199c.2.2.2
                                        linarith only [h136, hc45, hlam, hphi, ht0b, ht5b, p199_1]
                                      · have p199_0 := h199c.1
                                        have p199_1 := h199c.2.1
                                        have p199_2 := h199c.2.2.1
                                        have p199_3 := h199c.2.2.2
                                        linarith only [h2, hlam, p199_0]
                                      · have p199_0 := h199c.1
                                        have p199_1 := h199c.2.1
                                        have p199_2 := h199c.2.2.1
                                        have p199_3 := h199c.2.2.2
                                        linarith only [hlam, p199_0]
                                      · have p199_0 := h199c.1
                                        have p199_1 := h199c.2.1
                                        have p199_2 := h199c.2.2.1
                                        have p199_3 := h199c.2.2.2
                                        linarith only [h132, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p199_1, u2ehi2]
                                      · have p199_0 := h199c.1
                                        have p199_1 := h199c.2.1
                                        have p199_2 := h199c.2.2.1
                                        have p199_3 := h199c.2.2.2
                                        linarith only [h127, hlam, p199_1]
                                      · have p199_0 := h199c.1
                                        have p199_1 := h199c.2.1
                                        have p199_2 := h199c.2.2.1
                                        have p199_3 := h199c.2.2.2
                                        linarith only [h0, h123, h129, hc01, hc45, hlam, hphi, ht0b, ht5b, p199_1]
                                      · have p199_0 := h199c.1
                                        have p199_1 := h199c.2.1
                                        have p199_2 := h199c.2.2.1
                                        have p199_3 := h199c.2.2.2
                                        linarith only [h4, hlam, p199_1]
                                      · have p199_0 := h199c.1
                                        have p199_1 := h199c.2.1
                                        have p199_2 := h199c.2.2.1
                                        have p199_3 := h199c.2.2.2
                                        linarith only [h124, hlam, p199_1]
                                      · have p199_0 := h199c.1
                                        have p199_1 := h199c.2.1
                                        have p199_2 := h199c.2.2.1
                                        have p199_3 := h199c.2.2.2
                                        linarith only [hlam, p199_0]
                                      · have p199_0 := h199c.1
                                        have p199_1 := h199c.2.1
                                        have p199_2 := h199c.2.2.1
                                        have p199_3 := h199c.2.2.2
                                        linarith only [h132, hlam, p199_1]
                                      · have p199_0 := h199c.1
                                        have p199_1 := h199c.2.1
                                        have p199_2 := h199c.2.2.1
                                        have p199_3 := h199c.2.2.2
                                        linarith only [h0, h4, hc01, hc45, hlam, hphi, ht0b, ht5b, p199_1]
                                      · have p199_0 := h199c.1
                                        have p199_1 := h199c.2.1
                                        have p199_2 := h199c.2.2.1
                                        have p199_3 := h199c.2.2.2
                                        linarith only [h135, h4, hc34, hlam, hphi, ht23, p199_1, u2ehi4]
                                      · have p199_0 := h199c.1
                                        have p199_1 := h199c.2.1
                                        have p199_2 := h199c.2.2.1
                                        have p199_3 := h199c.2.2.2
                                        linarith only [h124, h135, hc34, hlam, hphi, ht23, p199_1, u2ehi4]
                                      · have p199_0 := h199c.1
                                        have p199_1 := h199c.2.1
                                        have p199_2 := h199c.2.2.1
                                        have p199_3 := h199c.2.2.2
                                        linarith only [h135, hc34, hlam, hphi, ht23, p199_1, u2ehi4]
                                      · have p199_0 := h199c.1
                                        have p199_1 := h199c.2.1
                                        have p199_2 := h199c.2.2.1
                                        have p199_3 := h199c.2.2.2
                                        linarith only [hlam, p199_0]
                                      · have p199_0 := h199c.1
                                        have p199_1 := h199c.2.1
                                        have p199_2 := h199c.2.2.1
                                        have p199_3 := h199c.2.2.2
                                        rcases p199_3 (m.d 0 5) (by simp) with h219 | h219
                                        · linarith only [h119, h219, hlam]
                                        · linarith only [h121, h219, hlam]
                                      · have p199_0 := h199c.1
                                        have p199_1 := h199c.2.1
                                        have p199_2 := h199c.2.2.1
                                        have p199_3 := h199c.2.2.2
                                        linarith only [h121, hlam, p199_0]
                                      · have p199_0 := h199c.1
                                        have p199_1 := h199c.2.1
                                        have p199_2 := h199c.2.2.1
                                        have p199_3 := h199c.2.2.2
                                        linarith only [h129, hlam, p199_0]
                                      · have p199_0 := h199c.1
                                        have p199_1 := h199c.2.1
                                        have p199_2 := h199c.2.2.1
                                        have p199_3 := h199c.2.2.2
                                        linarith only [h134, hlam, p199_0]
                                      · have p199_0 := h199c.1
                                        have p199_1 := h199c.2.1
                                        have p199_2 := h199c.2.2.1
                                        have p199_3 := h199c.2.2.2
                                        linarith only [h135, hlam, p199_0]
                                      · have p199_0 := h199c.1
                                        have p199_1 := h199c.2.1
                                        have p199_2 := h199c.2.2.1
                                        have p199_3 := h199c.2.2.2
                                        linarith only [hlam, p199_0]
                                  · linarith only [h1, h122, h135, h5, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                                · linarith only [h121, h134, h5, hc34, hlam, hphi, ht23, u2ehi3]
                          · linarith only [h121, h123, h129, h5, hc34, hlam, hphi, ht23, u2ehi3]
                    · linarith only [h0, h122, h124, h4, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                  · linarith only [h122, h123, hc24, hlam, hphi, u2ehi2]
                · linarith only [h122, h3, h5, hc34, hlam, hphi, ht23, u2ehi1]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h233 | h233
                · rcases m.htr 1 2 4 (by decide) (by decide) with h234 | h234
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h235 | h235
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h236 | h236
                      · linarith only [h1, h121, h236, h5, hc45, hlam, hphi, ht34, u3ehi3]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h238 | h238
                        · linarith only [h1, h119, h238, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h240 | h240
                          · linarith only [h0, h121, h234, h240, h5, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h242 | h242
                            · linarith only [h1, h233, h242, h5, hlam]
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h244 | h244
                              · linarith only [h1, h119, h233, h244, hlam]
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h246 | h246
                                · linarith only [h0, h1, h121, h233, h234, h246, h5, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h248 | h248
                                  · linarith only [h1, h121, h233, h248, h5, hc34, hlam, hphi, ht23, u2ehi2]
                                  · linarith only [h1, h233, h248, h5, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                    · linarith only [h0, h233, h235, h4, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                  · linarith only [h233, h234, hc24, hlam, hphi, u2ehi2]
                · linarith only [h233, h3, h5, hc34, hlam, hphi, ht23, u2ehi1]
        · linarith only [h3, h4, hc25, hlam, hphi, u2ehi2]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h255 | h255
        · linarith only [h255, h3, hc23, hlam, hphi, u2ehi4]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h257 | h257
          · rcases m.htr 0 3 5 (by decide) (by decide) with h258 | h258
            · rcases m.htr 0 4 5 (by decide) (by decide) with h259 | h259
              · rcases m.htr 1 2 3 (by decide) (by decide) with h260 | h260
                · linarith only [h0, h260, h3, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h262 | h262
                  · linarith only [h0, h262, h3, hc23, hlam, hphi, u2ehi3]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h264 | h264
                    · linarith only [h0, h255, h264, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h266 | h266
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h267 | h267
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h268 | h268
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h269 | h269
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h270 | h270
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h271 | h271
                                · rcases m.htr 3 4 5 (by decide) (by decide) with h272 | h272
                                  · rcases h0emax with h273 | h273 | h273 | h273 | h273
                                    · linarith only [h0, h273, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                                    · rcases h5bigk with h275c | h275c | h275c | h275c | h275c | h275c | h275c | h275c | h275c | h275c | h275c | h275c | h275c | h275c | h275c | h275c | h275c | h275c | h275c | h275c | h275c | h275c | h275c | h275c | h275c
                                      · have p275_0 := h275c.1
                                        have p275_1 := h275c.2.1
                                        have p275_2 := h275c.2.2.1
                                        have p275_3 := h275c.2.2.2
                                        linarith only [hlam, p275_0]
                                      · have p275_0 := h275c.1
                                        have p275_1 := h275c.2.1
                                        have p275_2 := h275c.2.2.1
                                        have p275_3 := h275c.2.2.2
                                        linarith only [h259, h264, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p275_1, u2ehi1]
                                      · have p275_0 := h275c.1
                                        have p275_1 := h275c.2.1
                                        have p275_2 := h275c.2.2.1
                                        have p275_3 := h275c.2.2.2
                                        linarith only [h255, hlam, p275_0]
                                      · have p275_0 := h275c.1
                                        have p275_1 := h275c.2.1
                                        have p275_2 := h275c.2.2.1
                                        have p275_3 := h275c.2.2.2
                                        linarith only [hc05, hlam, hphi, ht0b, ht34, ht45, ht5b, p275_1, u3ehi4]
                                      · have p275_0 := h275c.1
                                        have p275_1 := h275c.2.1
                                        have p275_2 := h275c.2.2.1
                                        have p275_3 := h275c.2.2.2
                                        rcases p275_3 (m.d 0 5) (by simp) with h280 | h280
                                        · rcases p275_3 (m.d 1 5) (by simp) with h281 | h281
                                          · linarith only [h2, h281, hlam]
                                          · linarith only [h268, h281, hlam]
                                        · linarith only [h259, h280, hlam]
                                      · have p275_0 := h275c.1
                                        have p275_1 := h275c.2.1
                                        have p275_2 := h275c.2.2.1
                                        have p275_3 := h275c.2.2.2
                                        linarith only [h2, hlam, p275_0]
                                      · have p275_0 := h275c.1
                                        have p275_1 := h275c.2.1
                                        have p275_2 := h275c.2.2.1
                                        have p275_3 := h275c.2.2.2
                                        linarith only [hlam, p275_0]
                                      · have p275_0 := h275c.1
                                        have p275_1 := h275c.2.1
                                        have p275_2 := h275c.2.2.1
                                        have p275_3 := h275c.2.2.2
                                        linarith only [h264, hlam, p275_0]
                                      · have p275_0 := h275c.1
                                        have p275_1 := h275c.2.1
                                        have p275_2 := h275c.2.2.1
                                        have p275_3 := h275c.2.2.2
                                        linarith only [h268, hc14, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p275_1, u3ehi4]
                                      · have p275_0 := h275c.1
                                        have p275_1 := h275c.2.1
                                        have p275_2 := h275c.2.2.1
                                        have p275_3 := h275c.2.2.2
                                        linarith only [h1, h266, h268, hc01, hc45, hlam, hphi, ht0b, ht5b, p275_1]
                                      · have p275_0 := h275c.1
                                        have p275_1 := h275c.2.1
                                        have p275_2 := h275c.2.2.1
                                        have p275_3 := h275c.2.2.2
                                        linarith only [h0, h255, h269, h271, hc23, hlam, hphi, p275_1, u2ehi1]
                                      · have p275_0 := h275c.1
                                        have p275_1 := h275c.2.1
                                        have p275_2 := h275c.2.2.1
                                        have p275_3 := h275c.2.2.2
                                        linarith only [h264, h269, h271, hc23, hlam, hphi, p275_1, u2ehi1]
                                      · have p275_0 := h275c.1
                                        have p275_1 := h275c.2.1
                                        have p275_2 := h275c.2.2.1
                                        have p275_3 := h275c.2.2.2
                                        linarith only [hlam, p275_0]
                                      · have p275_0 := h275c.1
                                        have p275_1 := h275c.2.1
                                        have p275_2 := h275c.2.2.1
                                        have p275_3 := h275c.2.2.2
                                        linarith only [h269, h271, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p275_1, u3ehi4]
                                      · have p275_0 := h275c.1
                                        have p275_1 := h275c.2.1
                                        have p275_2 := h275c.2.2.1
                                        have p275_3 := h275c.2.2.2
                                        rcases p275_3 (m.d 0 5) (by simp) with h294 | h294
                                        · linarith only [h255, h294, hlam]
                                        · linarith only [h259, h294, hlam]
                                      · have p275_0 := h275c.1
                                        have p275_1 := h275c.2.1
                                        have p275_2 := h275c.2.2.1
                                        have p275_3 := h275c.2.2.2
                                        linarith only [h258, hlam, p275_0]
                                      · have p275_0 := h275c.1
                                        have p275_1 := h275c.2.1
                                        have p275_2 := h275c.2.2.1
                                        have p275_3 := h275c.2.2.2
                                        linarith only [h267, hlam, p275_0]
                                      · have p275_0 := h275c.1
                                        have p275_1 := h275c.2.1
                                        have p275_2 := h275c.2.2.1
                                        have p275_3 := h275c.2.2.2
                                        linarith only [h270, hlam, p275_0]
                                      · have p275_0 := h275c.1
                                        have p275_1 := h275c.2.1
                                        have p275_2 := h275c.2.2.1
                                        have p275_3 := h275c.2.2.2
                                        linarith only [hlam, p275_0]
                                      · have p275_0 := h275c.1
                                        have p275_1 := h275c.2.1
                                        have p275_2 := h275c.2.2.1
                                        have p275_3 := h275c.2.2.2
                                        linarith only [h257, h272, h3, hc23, hc45, hlam, hphi, ht01, ht0b, ht12, ht5b, p275_1]
                                      · have p275_0 := h275c.1
                                        have p275_1 := h275c.2.1
                                        have p275_2 := h275c.2.2.1
                                        have p275_3 := h275c.2.2.2
                                        linarith only [h259, hlam, p275_0]
                                      · have p275_0 := h275c.1
                                        have p275_1 := h275c.2.1
                                        have p275_2 := h275c.2.2.1
                                        have p275_3 := h275c.2.2.2
                                        linarith only [h268, hlam, p275_0]
                                      · have p275_0 := h275c.1
                                        have p275_1 := h275c.2.1
                                        have p275_2 := h275c.2.2.1
                                        have p275_3 := h275c.2.2.2
                                        linarith only [h271, hlam, p275_0]
                                      · have p275_0 := h275c.1
                                        have p275_1 := h275c.2.1
                                        have p275_2 := h275c.2.2.1
                                        have p275_3 := h275c.2.2.2
                                        linarith only [h272, hlam, p275_0]
                                      · have p275_0 := h275c.1
                                        have p275_1 := h275c.2.1
                                        have p275_2 := h275c.2.2.1
                                        have p275_3 := h275c.2.2.2
                                        linarith only [hlam, p275_0]
                                    · linarith only [h1, h266, h273, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                                    · rcases h5bigk with h308c | h308c | h308c | h308c | h308c | h308c | h308c | h308c | h308c | h308c | h308c | h308c | h308c | h308c | h308c | h308c | h308c | h308c | h308c | h308c | h308c | h308c | h308c | h308c | h308c
                                      · have p308_0 := h308c.1
                                        have p308_1 := h308c.2.1
                                        have p308_2 := h308c.2.2.1
                                        have p308_3 := h308c.2.2.2
                                        linarith only [hlam, p308_0]
                                      · have p308_0 := h308c.1
                                        have p308_1 := h308c.2.1
                                        have p308_2 := h308c.2.2.1
                                        have p308_3 := h308c.2.2.2
                                        linarith only [h259, h264, h273, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p308_1, u2ehi1]
                                      · have p308_0 := h308c.1
                                        have p308_1 := h308c.2.1
                                        have p308_2 := h308c.2.2.1
                                        have p308_3 := h308c.2.2.2
                                        linarith only [h255, hlam, p308_0]
                                      · have p308_0 := h308c.1
                                        have p308_1 := h308c.2.1
                                        have p308_2 := h308c.2.2.1
                                        have p308_3 := h308c.2.2.2
                                        linarith only [h259, h273, hlam, hphi, ht0b, ht34, ht45, ht5b, p308_1, u3ehi4]
                                      · have p308_0 := h308c.1
                                        have p308_1 := h308c.2.1
                                        have p308_2 := h308c.2.2.1
                                        have p308_3 := h308c.2.2.2
                                        linarith only [h259, h273, hc45, hlam, hphi, ht0b, ht5b, p308_1]
                                      · have p308_0 := h308c.1
                                        have p308_1 := h308c.2.1
                                        have p308_2 := h308c.2.2.1
                                        have p308_3 := h308c.2.2.2
                                        linarith only [h2, hlam, p308_0]
                                      · have p308_0 := h308c.1
                                        have p308_1 := h308c.2.1
                                        have p308_2 := h308c.2.2.1
                                        have p308_3 := h308c.2.2.2
                                        linarith only [hlam, p308_0]
                                      · have p308_0 := h308c.1
                                        have p308_1 := h308c.2.1
                                        have p308_2 := h308c.2.2.1
                                        have p308_3 := h308c.2.2.2
                                        linarith only [h264, hlam, p308_0]
                                      · have p308_0 := h308c.1
                                        have p308_1 := h308c.2.1
                                        have p308_2 := h308c.2.2.1
                                        have p308_3 := h308c.2.2.2
                                        linarith only [hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p308_1, u3ehi4]
                                      · have p308_0 := h308c.1
                                        have p308_1 := h308c.2.1
                                        have p308_2 := h308c.2.2.1
                                        have p308_3 := h308c.2.2.2
                                        linarith only [h2, h259, h273, hc45, hlam, hphi, ht0b, ht5b, p308_1]
                                      · have p308_0 := h308c.1
                                        have p308_1 := h308c.2.1
                                        have p308_2 := h308c.2.2.1
                                        have p308_3 := h308c.2.2.2
                                        linarith only [h0, h255, h269, h271, hc23, hlam, hphi, p308_1, u2ehi1]
                                      · have p308_0 := h308c.1
                                        have p308_1 := h308c.2.1
                                        have p308_2 := h308c.2.2.1
                                        have p308_3 := h308c.2.2.2
                                        linarith only [h264, h269, h271, hc23, hlam, hphi, p308_1, u2ehi1]
                                      · have p308_0 := h308c.1
                                        have p308_1 := h308c.2.1
                                        have p308_2 := h308c.2.2.1
                                        have p308_3 := h308c.2.2.2
                                        linarith only [hlam, p308_0]
                                      · have p308_0 := h308c.1
                                        have p308_1 := h308c.2.1
                                        have p308_2 := h308c.2.2.1
                                        have p308_3 := h308c.2.2.2
                                        linarith only [h269, h271, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p308_1, u3ehi4]
                                      · have p308_0 := h308c.1
                                        have p308_1 := h308c.2.1
                                        have p308_2 := h308c.2.2.1
                                        have p308_3 := h308c.2.2.2
                                        rcases p308_3 (m.d 0 5) (by simp) with h323 | h323
                                        · linarith only [h255, h323, hlam]
                                        · linarith only [h259, h323, hlam]
                                      · have p308_0 := h308c.1
                                        have p308_1 := h308c.2.1
                                        have p308_2 := h308c.2.2.1
                                        have p308_3 := h308c.2.2.2
                                        linarith only [h258, hlam, p308_0]
                                      · have p308_0 := h308c.1
                                        have p308_1 := h308c.2.1
                                        have p308_2 := h308c.2.2.1
                                        have p308_3 := h308c.2.2.2
                                        linarith only [h267, hlam, p308_0]
                                      · have p308_0 := h308c.1
                                        have p308_1 := h308c.2.1
                                        have p308_2 := h308c.2.2.1
                                        have p308_3 := h308c.2.2.2
                                        linarith only [h270, hlam, p308_0]
                                      · have p308_0 := h308c.1
                                        have p308_1 := h308c.2.1
                                        have p308_2 := h308c.2.2.1
                                        have p308_3 := h308c.2.2.2
                                        linarith only [hlam, p308_0]
                                      · have p308_0 := h308c.1
                                        have p308_1 := h308c.2.1
                                        have p308_2 := h308c.2.2.1
                                        have p308_3 := h308c.2.2.2
                                        linarith only [h1, h266, h272, hc03, hc45, hlam, hphi, ht0b, ht5b, p308_1]
                                      · have p308_0 := h308c.1
                                        have p308_1 := h308c.2.1
                                        have p308_2 := h308c.2.2.1
                                        have p308_3 := h308c.2.2.2
                                        linarith only [h259, hlam, p308_0]
                                      · have p308_0 := h308c.1
                                        have p308_1 := h308c.2.1
                                        have p308_2 := h308c.2.2.1
                                        have p308_3 := h308c.2.2.2
                                        linarith only [h268, hlam, p308_0]
                                      · have p308_0 := h308c.1
                                        have p308_1 := h308c.2.1
                                        have p308_2 := h308c.2.2.1
                                        have p308_3 := h308c.2.2.2
                                        linarith only [h271, hlam, p308_0]
                                      · have p308_0 := h308c.1
                                        have p308_1 := h308c.2.1
                                        have p308_2 := h308c.2.2.1
                                        have p308_3 := h308c.2.2.2
                                        linarith only [h272, hlam, p308_0]
                                      · have p308_0 := h308c.1
                                        have p308_1 := h308c.2.1
                                        have p308_2 := h308c.2.2.1
                                        have p308_3 := h308c.2.2.2
                                        linarith only [hlam, p308_0]
                                    · rcases h5bigk with h336c | h336c | h336c | h336c | h336c | h336c | h336c | h336c | h336c | h336c | h336c | h336c | h336c | h336c | h336c | h336c | h336c | h336c | h336c | h336c | h336c | h336c | h336c | h336c | h336c
                                      · have p336_0 := h336c.1
                                        have p336_1 := h336c.2.1
                                        have p336_2 := h336c.2.2.1
                                        have p336_3 := h336c.2.2.2
                                        linarith only [hlam, p336_0]
                                      · have p336_0 := h336c.1
                                        have p336_1 := h336c.2.1
                                        have p336_2 := h336c.2.2.1
                                        have p336_3 := h336c.2.2.2
                                        linarith only [h264, h273, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p336_1, u2ehi1]
                                      · have p336_0 := h336c.1
                                        have p336_1 := h336c.2.1
                                        have p336_2 := h336c.2.2.1
                                        have p336_3 := h336c.2.2.2
                                        linarith only [h255, hlam, p336_0]
                                      · have p336_0 := h336c.1
                                        have p336_1 := h336c.2.1
                                        have p336_2 := h336c.2.2.1
                                        have p336_3 := h336c.2.2.2
                                        linarith only [h273, hlam, hphi, ht0b, ht34, ht45, ht5b, p336_1, u3ehi4]
                                      · have p336_0 := h336c.1
                                        have p336_1 := h336c.2.1
                                        have p336_2 := h336c.2.2.1
                                        have p336_3 := h336c.2.2.2
                                        linarith only [h273, hc45, hlam, hphi, ht0b, ht5b, p336_1]
                                      · have p336_0 := h336c.1
                                        have p336_1 := h336c.2.1
                                        have p336_2 := h336c.2.2.1
                                        have p336_3 := h336c.2.2.2
                                        linarith only [h2, hlam, p336_0]
                                      · have p336_0 := h336c.1
                                        have p336_1 := h336c.2.1
                                        have p336_2 := h336c.2.2.1
                                        have p336_3 := h336c.2.2.2
                                        linarith only [hlam, p336_0]
                                      · have p336_0 := h336c.1
                                        have p336_1 := h336c.2.1
                                        have p336_2 := h336c.2.2.1
                                        have p336_3 := h336c.2.2.2
                                        linarith only [h264, hlam, p336_0]
                                      · have p336_0 := h336c.1
                                        have p336_1 := h336c.2.1
                                        have p336_2 := h336c.2.2.1
                                        have p336_3 := h336c.2.2.2
                                        linarith only [hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p336_1, u3ehi4]
                                      · have p336_0 := h336c.1
                                        have p336_1 := h336c.2.1
                                        have p336_2 := h336c.2.2.1
                                        have p336_3 := h336c.2.2.2
                                        linarith only [h2, h273, hc45, hlam, hphi, ht0b, ht5b, p336_1]
                                      · have p336_0 := h336c.1
                                        have p336_1 := h336c.2.1
                                        have p336_2 := h336c.2.2.1
                                        have p336_3 := h336c.2.2.2
                                        linarith only [h0, h255, h269, h271, hc23, hlam, hphi, p336_1, u2ehi1]
                                      · have p336_0 := h336c.1
                                        have p336_1 := h336c.2.1
                                        have p336_2 := h336c.2.2.1
                                        have p336_3 := h336c.2.2.2
                                        linarith only [h264, h269, h271, hc23, hlam, hphi, p336_1, u2ehi1]
                                      · have p336_0 := h336c.1
                                        have p336_1 := h336c.2.1
                                        have p336_2 := h336c.2.2.1
                                        have p336_3 := h336c.2.2.2
                                        linarith only [hlam, p336_0]
                                      · have p336_0 := h336c.1
                                        have p336_1 := h336c.2.1
                                        have p336_2 := h336c.2.2.1
                                        have p336_3 := h336c.2.2.2
                                        linarith only [h269, h271, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p336_1, u3ehi4]
                                      · have p336_0 := h336c.1
                                        have p336_1 := h336c.2.1
                                        have p336_2 := h336c.2.2.1
                                        have p336_3 := h336c.2.2.2
                                        rcases p336_3 (m.d 0 5) (by simp) with h351 | h351
                                        · linarith only [h255, h351, hlam]
                                        · linarith only [h259, h351, hlam]
                                      · have p336_0 := h336c.1
                                        have p336_1 := h336c.2.1
                                        have p336_2 := h336c.2.2.1
                                        have p336_3 := h336c.2.2.2
                                        linarith only [h258, hlam, p336_0]
                                      · have p336_0 := h336c.1
                                        have p336_1 := h336c.2.1
                                        have p336_2 := h336c.2.2.1
                                        have p336_3 := h336c.2.2.2
                                        linarith only [h267, hlam, p336_0]
                                      · have p336_0 := h336c.1
                                        have p336_1 := h336c.2.1
                                        have p336_2 := h336c.2.2.1
                                        have p336_3 := h336c.2.2.2
                                        linarith only [h270, hlam, p336_0]
                                      · have p336_0 := h336c.1
                                        have p336_1 := h336c.2.1
                                        have p336_2 := h336c.2.2.1
                                        have p336_3 := h336c.2.2.2
                                        linarith only [hlam, p336_0]
                                      · have p336_0 := h336c.1
                                        have p336_1 := h336c.2.1
                                        have p336_2 := h336c.2.2.1
                                        have p336_3 := h336c.2.2.2
                                        linarith only [h266, h272, hc13, hc45, hlam, hphi, ht01, ht0b, ht5b, p336_1]
                                      · have p336_0 := h336c.1
                                        have p336_1 := h336c.2.1
                                        have p336_2 := h336c.2.2.1
                                        have p336_3 := h336c.2.2.2
                                        linarith only [h259, hlam, p336_0]
                                      · have p336_0 := h336c.1
                                        have p336_1 := h336c.2.1
                                        have p336_2 := h336c.2.2.1
                                        have p336_3 := h336c.2.2.2
                                        linarith only [h268, hlam, p336_0]
                                      · have p336_0 := h336c.1
                                        have p336_1 := h336c.2.1
                                        have p336_2 := h336c.2.2.1
                                        have p336_3 := h336c.2.2.2
                                        linarith only [h271, hlam, p336_0]
                                      · have p336_0 := h336c.1
                                        have p336_1 := h336c.2.1
                                        have p336_2 := h336c.2.2.1
                                        have p336_3 := h336c.2.2.2
                                        linarith only [h272, hlam, p336_0]
                                      · have p336_0 := h336c.1
                                        have p336_1 := h336c.2.1
                                        have p336_2 := h336c.2.2.1
                                        have p336_3 := h336c.2.2.2
                                        linarith only [hlam, p336_0]
                                  · linarith only [h1, h266, h268, h272, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                                · linarith only [h1, h266, h268, h271, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                              · linarith only [h0, h2, h267, h270, h3, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                            · linarith only [h1, h267, h269, h3, hc34, hlam, hphi, u3ehi4]
                          · linarith only [h257, h259, h262, h268, h3, hc23, hlam, hphi, u2ehi1]
                        · linarith only [h266, h267, hc35, hlam, hphi, u3ehi3]
                      · linarith only [h257, h260, h266, h3, hc23, hlam, hphi, u2ehi1]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h371 | h371
                · linarith only [h0, h3, h371, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h373 | h373
                  · linarith only [h0, h3, h373, hc23, hlam, hphi, u2ehi3]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h375 | h375
                    · linarith only [h0, h3, h375, hc23, hlam, hphi, u2ehi4]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h377 | h377
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h378 | h378
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h379 | h379
                          · linarith only [h1, h257, h259, h377, h379, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h381 | h381
                            · rcases m.htr 2 3 5 (by decide) (by decide) with h382 | h382
                              · rcases m.htr 2 4 5 (by decide) (by decide) with h383 | h383
                                · linarith only [h373, h379, h381, h383, hc23, hlam, hphi, u2ehi1]
                                · linarith only [h373, h383, hc45, hlam, hphi, ht23, ht34, u2ehi1]
                              · linarith only [h1, h378, h382, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                            · linarith only [h0, h3, h381, hc34, hlam, hphi, ht23, u2ehi1]
                        · linarith only [h258, h3, h371, h378, hc23, hlam, hphi, u2ehi1]
                      · linarith only [h257, h259, h371, h377, hc45, hlam, hphi, ht23, ht34, u2ehi1]
            · linarith only [h257, h258, hc35, hlam, hphi, u3ehi3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h391 | h391
            · linarith only [h257, h391, hc34, hlam, hphi, u3ehi4]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h393 | h393
              · rcases m.htr 1 2 3 (by decide) (by decide) with h394 | h394
                · linarith only [h0, h255, h394, hc25, hlam, hphi, u2ehi2]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h396 | h396
                  · linarith only [h0, h257, h3, h396, hc34, hlam, hphi, ht23, u2ehi3]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h398 | h398
                    · linarith only [h0, h255, h398, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h400 | h400
                      · linarith only [h1, h257, h3, h400, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h402 | h402
                        · linarith only [h1, h391, h402, hlam]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h404 | h404
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h405 | h405
                            · linarith only [h0, h257, h3, h405, hc23, hlam, hphi, u2ehi1]
                            · linarith only [h0, h3, h405, hc34, hlam, hphi, ht23, u2ehi1]
                          · linarith only [h257, h393, h396, h404, hc34, hlam, hphi, ht23, u2ehi1]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h409 | h409
                · linarith only [h0, h3, h409, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h411 | h411
                  · linarith only [h0, h3, h411, hc23, hlam, hphi, u2ehi3]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h413 | h413
                    · linarith only [h0, h255, h413, hlam]
                    · rcases m.htr 1 3 4 (by decide) (by decide) with h415 | h415
                      · linarith only [h1, h257, h393, h415, hc45, hlam, hphi, ht34, u3ehi3]
                      · rcases m.htr 1 3 5 (by decide) (by decide) with h417 | h417
                        · linarith only [h1, h257, h393, h417, hc45, hlam, hphi, ht34, u3ehi4]
                        · rcases m.htr 1 4 5 (by decide) (by decide) with h419 | h419
                          · linarith only [h257, h3, h393, h411, h419, hc24, hlam, hphi, u2ehi0]
                          · rcases m.htr 2 3 4 (by decide) (by decide) with h421 | h421
                            · linarith only [h0, h257, h3, h421, hc23, hlam, hphi, u2ehi1]
                            · linarith only [h0, h3, h421, hc34, hlam, hphi, ht23, u2ehi1]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h424 | h424
      · rcases m.htr 0 2 5 (by decide) (by decide) with h425 | h425
        · linarith only [h0, h2, h425, hlam]
        · linarith only [h424, h425, hc25, hlam, hphi, u2ehi2]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h428 | h428
        · linarith only [h424, h428, hc23, hlam, hphi, u2ehi4]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h430 | h430
          · rcases m.htr 0 3 5 (by decide) (by decide) with h431 | h431
            · linarith only [h1, h2, h431, hlam]
            · linarith only [h430, h431, hc35, hlam, hphi, u3ehi3]
          · rcases m.htr 0 3 5 (by decide) (by decide) with h434 | h434
            · linarith only [h430, h434, hc34, hlam, hphi, u3ehi4]
            · rcases m.htr 0 4 5 (by decide) (by decide) with h436 | h436
              · rcases m.htr 1 2 3 (by decide) (by decide) with h437 | h437
                · linarith only [h0, h424, h437, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h439 | h439
                  · linarith only [h1, h2, h437, h439, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h441 | h441
                    · linarith only [h1, h2, h437, h441, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi4]
                    · linarith only [h1, h2, h437, h441, hc25, hlam, hphi, u2ehi1]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h444 | h444
                · linarith only [h0, h424, h444, hlam]
                · rcases m.htr 1 2 4 (by decide) (by decide) with h446 | h446
                  · linarith only [h1, h2, h444, h446, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                  · rcases m.htr 1 2 5 (by decide) (by decide) with h448 | h448
                    · linarith only [h1, h2, h444, h448, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi4]
                    · linarith only [h1, h2, h444, h448, hc25, hlam, hphi, u2ehi1]
  · rcases m.htr 0 1 5 (by decide) (by decide) with h451 | h451
    · rcases m.htr 0 2 3 (by decide) (by decide) with h452 | h452
      · linarith only [h0, h1, h452, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h454 | h454
        · linarith only [h452, h454, hc23, hlam, hphi, u2ehi4]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h456 | h456
          · rcases m.htr 0 3 5 (by decide) (by decide) with h457 | h457
            · rcases m.htr 0 4 5 (by decide) (by decide) with h458 | h458
              · rcases m.htr 1 2 3 (by decide) (by decide) with h459 | h459
                · linarith only [h0, h1, h452, h459, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                · linarith only [h0, h1, h459, hc23, hlam, hphi, u2ehi1]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h462 | h462
                · linarith only [h0, h1, h462, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                · linarith only [h0, h1, h462, hc23, hlam, hphi, u2ehi1]
            · linarith only [h0, h1, h457, hc35, hlam, hphi, ht23, u2ehi1]
          · linarith only [h0, h1, h456, hc34, hlam, hphi, ht23, u2ehi1]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h467 | h467
      · linarith only [h0, h1, h467, hlam]
      · rcases m.htr 0 2 5 (by decide) (by decide) with h469 | h469
        · linarith only [h467, h469, hc23, hlam, hphi, u2ehi4]
        · rcases m.htr 0 3 4 (by decide) (by decide) with h471 | h471
          · rcases m.htr 0 3 5 (by decide) (by decide) with h472 | h472
            · rcases m.htr 0 4 5 (by decide) (by decide) with h473 | h473
              · rcases m.htr 1 2 3 (by decide) (by decide) with h474 | h474
                · linarith only [h0, h1, h467, h474, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi0]
                · linarith only [h0, h1, h474, hc23, hlam, hphi, u2ehi1]
              · rcases m.htr 1 2 3 (by decide) (by decide) with h477 | h477
                · linarith only [h0, h1, h467, h477, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                · linarith only [h0, h1, h477, hc23, hlam, hphi, u2ehi1]
            · linarith only [h0, h1, h472, hc35, hlam, hphi, ht23, u2ehi1]
          · linarith only [h0, h1, h471, hc34, hlam, hphi, ht23, u2ehi1]

set_option maxHeartbeats 4664000 in
theorem r1l7_10_12_13_25_L_I_L_R_L_R_H_I_x1_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h482 : (m.d 0 1 + m.lam ≤ m.d 1 3 ∧ m.d 0 1 < m.d 0 3 ∧ m.d 0 3 < m.d 1 3))
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
  have h0emax := hb0.2.2
  have h2ehi := hb2.1
  have h3ehi := hb3.1
  have h5bigk := hb5.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 1 5 (by decide) (by decide) with h483 | h483
  · rcases m.htr 0 2 3 (by decide) (by decide) with h484 | h484
    · rcases m.htr 0 2 5 (by decide) (by decide) with h485 | h485
      · rcases m.htr 0 3 4 (by decide) (by decide) with h486 | h486
        · rcases m.htr 0 3 5 (by decide) (by decide) with h487 | h487
          · rcases m.htr 0 4 5 (by decide) (by decide) with h488 | h488
            · rcases m.htr 1 2 3 (by decide) (by decide) with h489 | h489
              · rcases m.htr 1 2 4 (by decide) (by decide) with h490 | h490
                · rcases m.htr 1 2 5 (by decide) (by decide) with h491 | h491
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h492 | h492
                    · linarith only [h0, h482, h492, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                    · linarith only [h0, h482, h486, h489, h492, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                  · linarith only [h0, h482, h486, h491, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                · linarith only [h0, h482, h485, h486, h488, h490, hc24, hlam, hphi, u2ehi4]
              · linarith only [h0, h482, h486, h489, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h498 | h498
              · rcases m.htr 1 2 4 (by decide) (by decide) with h499 | h499
                · rcases m.htr 1 2 5 (by decide) (by decide) with h500 | h500
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h501 | h501
                    · linarith only [h0, h482, h501, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                    · linarith only [h0, h482, h486, h498, h501, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                  · linarith only [h499, h500, hc25, hlam, hphi, u2ehi3]
                · linarith only [h0, h482, h498, h499, hc24, hlam, hphi, u2ehi2]
              · linarith only [h0, h482, h498, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
          · linarith only [h486, h487, hc35, hlam, hphi, u3ehi3]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h508 | h508
          · linarith only [h486, h508, hc34, hlam, hphi, u3ehi4]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h510 | h510
            · rcases m.htr 1 2 3 (by decide) (by decide) with h511 | h511
              · rcases m.htr 1 2 4 (by decide) (by decide) with h512 | h512
                · rcases m.htr 1 2 5 (by decide) (by decide) with h513 | h513
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h514 | h514
                    · linarith only [h0, h482, h486, h514, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h516 | h516
                      · linarith only [h482, h508, h516, hlam]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h518 | h518
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h519 | h519
                          · linarith only [h0, h483, h511, h512, h514, h516, h519, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h521 | h521
                            · linarith only [h482, h508, h511, h521, hlam]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h523 | h523
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h524 | h524
                                · rcases h0emax with h525 | h525 | h525 | h525 | h525
                                  · linarith only [h483, h516, h525, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                                  · linarith only [h0, h483, h511, h516, h525, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                                  · rcases h5bigk with h528c | h528c | h528c | h528c | h528c | h528c | h528c | h528c | h528c | h528c | h528c | h528c | h528c | h528c | h528c | h528c | h528c | h528c | h528c | h528c | h528c | h528c | h528c | h528c | h528c
                                    · have p528_0 := h528c.1
                                      have p528_1 := h528c.2.1
                                      have p528_2 := h528c.2.2.1
                                      have p528_3 := h528c.2.2.2
                                      linarith only [hlam, p528_0]
                                    · have p528_0 := h528c.1
                                      have p528_1 := h528c.2.1
                                      have p528_2 := h528c.2.2.1
                                      have p528_3 := h528c.2.2.2
                                      linarith only [h510, h511, h516, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p528_1, u2ehi2]
                                    · have p528_0 := h528c.1
                                      have p528_1 := h528c.2.1
                                      have p528_2 := h528c.2.2.1
                                      have p528_3 := h528c.2.2.2
                                      linarith only [h0, h483, h521, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p528_1, u2ehi2]
                                    · have p528_0 := h528c.1
                                      have p528_1 := h528c.2.1
                                      have p528_2 := h528c.2.2.1
                                      have p528_3 := h528c.2.2.2
                                      linarith only [h508, hlam, p528_1]
                                    · have p528_0 := h528c.1
                                      have p528_1 := h528c.2.1
                                      have p528_2 := h528c.2.2.1
                                      have p528_3 := h528c.2.2.2
                                      linarith only [h0, h483, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p528_1]
                                    · have p528_0 := h528c.1
                                      have p528_1 := h528c.2.1
                                      have p528_2 := h528c.2.2.1
                                      have p528_3 := h528c.2.2.2
                                      linarith only [h483, hlam, p528_0]
                                    · have p528_0 := h528c.1
                                      have p528_1 := h528c.2.1
                                      have p528_2 := h528c.2.2.1
                                      have p528_3 := h528c.2.2.2
                                      linarith only [hlam, p528_0]
                                    · have p528_0 := h528c.1
                                      have p528_1 := h528c.2.1
                                      have p528_2 := h528c.2.2.1
                                      have p528_3 := h528c.2.2.2
                                      linarith only [h518, h521, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p528_1, u2ehi2]
                                    · have p528_0 := h528c.1
                                      have p528_1 := h528c.2.1
                                      have p528_2 := h528c.2.2.1
                                      have p528_3 := h528c.2.2.2
                                      linarith only [h516, hlam, p528_1]
                                    · have p528_0 := h528c.1
                                      have p528_1 := h528c.2.1
                                      have p528_2 := h528c.2.2.1
                                      have p528_3 := h528c.2.2.2
                                      linarith only [h483, hc01, hc45, hlam, hphi, ht0b, ht5b, p528_1]
                                    · have p528_0 := h528c.1
                                      have p528_1 := h528c.2.1
                                      have p528_2 := h528c.2.2.1
                                      have p528_3 := h528c.2.2.2
                                      linarith only [h485, hlam, p528_1]
                                    · have p528_0 := h528c.1
                                      have p528_1 := h528c.2.1
                                      have p528_2 := h528c.2.2.1
                                      have p528_3 := h528c.2.2.2
                                      linarith only [h513, hlam, p528_1]
                                    · have p528_0 := h528c.1
                                      have p528_1 := h528c.2.1
                                      have p528_2 := h528c.2.2.1
                                      have p528_3 := h528c.2.2.2
                                      linarith only [hlam, p528_0]
                                    · have p528_0 := h528c.1
                                      have p528_1 := h528c.2.1
                                      have p528_2 := h528c.2.2.1
                                      have p528_3 := h528c.2.2.2
                                      linarith only [h521, hlam, p528_1]
                                    · have p528_0 := h528c.1
                                      have p528_1 := h528c.2.1
                                      have p528_2 := h528c.2.2.1
                                      have p528_3 := h528c.2.2.2
                                      linarith only [h0, h485, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p528_1]
                                    · have p528_0 := h528c.1
                                      have p528_1 := h528c.2.1
                                      have p528_2 := h528c.2.2.1
                                      have p528_3 := h528c.2.2.2
                                      linarith only [h485, h524, hc34, hlam, hphi, ht23, p528_1, u2ehi4]
                                    · have p528_0 := h528c.1
                                      have p528_1 := h528c.2.1
                                      have p528_2 := h528c.2.2.1
                                      have p528_3 := h528c.2.2.2
                                      linarith only [h513, h524, hc34, hlam, hphi, ht23, p528_1, u2ehi4]
                                    · have p528_0 := h528c.1
                                      have p528_1 := h528c.2.1
                                      have p528_2 := h528c.2.2.1
                                      have p528_3 := h528c.2.2.2
                                      linarith only [h524, hc34, hlam, hphi, ht23, p528_1, u2ehi4]
                                    · have p528_0 := h528c.1
                                      have p528_1 := h528c.2.1
                                      have p528_2 := h528c.2.2.1
                                      have p528_3 := h528c.2.2.2
                                      linarith only [hlam, p528_0]
                                    · have p528_0 := h528c.1
                                      have p528_1 := h528c.2.1
                                      have p528_2 := h528c.2.2.1
                                      have p528_3 := h528c.2.2.2
                                      rcases p528_3 (m.d 0 5) (by simp) with h548 | h548
                                      · linarith only [h508, h548, hlam]
                                      · linarith only [h510, h548, hlam]
                                    · have p528_0 := h528c.1
                                      have p528_1 := h528c.2.1
                                      have p528_2 := h528c.2.2.1
                                      have p528_3 := h528c.2.2.2
                                      linarith only [h510, hlam, p528_0]
                                    · have p528_0 := h528c.1
                                      have p528_1 := h528c.2.1
                                      have p528_2 := h528c.2.2.1
                                      have p528_3 := h528c.2.2.2
                                      linarith only [h518, hlam, p528_0]
                                    · have p528_0 := h528c.1
                                      have p528_1 := h528c.2.1
                                      have p528_2 := h528c.2.2.1
                                      have p528_3 := h528c.2.2.2
                                      linarith only [h523, hlam, p528_0]
                                    · have p528_0 := h528c.1
                                      have p528_1 := h528c.2.1
                                      have p528_2 := h528c.2.2.1
                                      have p528_3 := h528c.2.2.2
                                      linarith only [h524, hlam, p528_0]
                                    · have p528_0 := h528c.1
                                      have p528_1 := h528c.2.1
                                      have p528_2 := h528c.2.2.1
                                      have p528_3 := h528c.2.2.2
                                      linarith only [hlam, p528_0]
                                  · rcases h5bigk with h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c | h556c
                                    · have p556_0 := h556c.1
                                      have p556_1 := h556c.2.1
                                      have p556_2 := h556c.2.2.1
                                      have p556_3 := h556c.2.2.2
                                      linarith only [hlam, p556_0]
                                    · have p556_0 := h556c.1
                                      have p556_1 := h556c.2.1
                                      have p556_2 := h556c.2.2.1
                                      have p556_3 := h556c.2.2.2
                                      linarith only [h511, h516, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p556_1, u2ehi2]
                                    · have p556_0 := h556c.1
                                      have p556_1 := h556c.2.1
                                      have p556_2 := h556c.2.2.1
                                      have p556_3 := h556c.2.2.2
                                      linarith only [h0, h483, h521, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p556_1, u2ehi2]
                                    · have p556_0 := h556c.1
                                      have p556_1 := h556c.2.1
                                      have p556_2 := h556c.2.2.1
                                      have p556_3 := h556c.2.2.2
                                      linarith only [h508, hlam, p556_1]
                                    · have p556_0 := h556c.1
                                      have p556_1 := h556c.2.1
                                      have p556_2 := h556c.2.2.1
                                      have p556_3 := h556c.2.2.2
                                      linarith only [h510, h525, hc45, hlam, hphi, ht0b, ht5b, p556_1]
                                    · have p556_0 := h556c.1
                                      have p556_1 := h556c.2.1
                                      have p556_2 := h556c.2.2.1
                                      have p556_3 := h556c.2.2.2
                                      linarith only [h483, hlam, p556_0]
                                    · have p556_0 := h556c.1
                                      have p556_1 := h556c.2.1
                                      have p556_2 := h556c.2.2.1
                                      have p556_3 := h556c.2.2.2
                                      linarith only [hlam, p556_0]
                                    · have p556_0 := h556c.1
                                      have p556_1 := h556c.2.1
                                      have p556_2 := h556c.2.2.1
                                      have p556_3 := h556c.2.2.2
                                      linarith only [h521, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p556_1, u2ehi2]
                                    · have p556_0 := h556c.1
                                      have p556_1 := h556c.2.1
                                      have p556_2 := h556c.2.2.1
                                      have p556_3 := h556c.2.2.2
                                      linarith only [h516, hlam, p556_1]
                                    · have p556_0 := h556c.1
                                      have p556_1 := h556c.2.1
                                      have p556_2 := h556c.2.2.1
                                      have p556_3 := h556c.2.2.2
                                      linarith only [h483, h510, h525, hc45, hlam, hphi, ht0b, ht5b, p556_1]
                                    · have p556_0 := h556c.1
                                      have p556_1 := h556c.2.1
                                      have p556_2 := h556c.2.2.1
                                      have p556_3 := h556c.2.2.2
                                      linarith only [h485, hlam, p556_1]
                                    · have p556_0 := h556c.1
                                      have p556_1 := h556c.2.1
                                      have p556_2 := h556c.2.2.1
                                      have p556_3 := h556c.2.2.2
                                      linarith only [h513, hlam, p556_1]
                                    · have p556_0 := h556c.1
                                      have p556_1 := h556c.2.1
                                      have p556_2 := h556c.2.2.1
                                      have p556_3 := h556c.2.2.2
                                      linarith only [hlam, p556_0]
                                    · have p556_0 := h556c.1
                                      have p556_1 := h556c.2.1
                                      have p556_2 := h556c.2.2.1
                                      have p556_3 := h556c.2.2.2
                                      linarith only [h521, hlam, p556_1]
                                    · have p556_0 := h556c.1
                                      have p556_1 := h556c.2.1
                                      have p556_2 := h556c.2.2.1
                                      have p556_3 := h556c.2.2.2
                                      linarith only [h0, h485, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p556_1]
                                    · have p556_0 := h556c.1
                                      have p556_1 := h556c.2.1
                                      have p556_2 := h556c.2.2.1
                                      have p556_3 := h556c.2.2.2
                                      linarith only [h485, h524, hc34, hlam, hphi, ht23, p556_1, u2ehi4]
                                    · have p556_0 := h556c.1
                                      have p556_1 := h556c.2.1
                                      have p556_2 := h556c.2.2.1
                                      have p556_3 := h556c.2.2.2
                                      linarith only [h513, h524, hc34, hlam, hphi, ht23, p556_1, u2ehi4]
                                    · have p556_0 := h556c.1
                                      have p556_1 := h556c.2.1
                                      have p556_2 := h556c.2.2.1
                                      have p556_3 := h556c.2.2.2
                                      linarith only [h524, hc34, hlam, hphi, ht23, p556_1, u2ehi4]
                                    · have p556_0 := h556c.1
                                      have p556_1 := h556c.2.1
                                      have p556_2 := h556c.2.2.1
                                      have p556_3 := h556c.2.2.2
                                      linarith only [hlam, p556_0]
                                    · have p556_0 := h556c.1
                                      have p556_1 := h556c.2.1
                                      have p556_2 := h556c.2.2.1
                                      have p556_3 := h556c.2.2.2
                                      rcases p556_3 (m.d 0 5) (by simp) with h576 | h576
                                      · linarith only [h508, h576, hlam]
                                      · linarith only [h510, h576, hlam]
                                    · have p556_0 := h556c.1
                                      have p556_1 := h556c.2.1
                                      have p556_2 := h556c.2.2.1
                                      have p556_3 := h556c.2.2.2
                                      linarith only [h510, hlam, p556_0]
                                    · have p556_0 := h556c.1
                                      have p556_1 := h556c.2.1
                                      have p556_2 := h556c.2.2.1
                                      have p556_3 := h556c.2.2.2
                                      linarith only [h518, hlam, p556_0]
                                    · have p556_0 := h556c.1
                                      have p556_1 := h556c.2.1
                                      have p556_2 := h556c.2.2.1
                                      have p556_3 := h556c.2.2.2
                                      linarith only [h523, hlam, p556_0]
                                    · have p556_0 := h556c.1
                                      have p556_1 := h556c.2.1
                                      have p556_2 := h556c.2.2.1
                                      have p556_3 := h556c.2.2.2
                                      linarith only [h524, hlam, p556_0]
                                    · have p556_0 := h556c.1
                                      have p556_1 := h556c.2.1
                                      have p556_2 := h556c.2.2.1
                                      have p556_3 := h556c.2.2.2
                                      linarith only [hlam, p556_0]
                                  · rcases h5bigk with h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c | h584c
                                    · have p584_0 := h584c.1
                                      have p584_1 := h584c.2.1
                                      have p584_2 := h584c.2.2.1
                                      have p584_3 := h584c.2.2.2
                                      linarith only [hlam, p584_0]
                                    · have p584_0 := h584c.1
                                      have p584_1 := h584c.2.1
                                      have p584_2 := h584c.2.2.1
                                      have p584_3 := h584c.2.2.2
                                      linarith only [h511, h516, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p584_1, u2ehi2]
                                    · have p584_0 := h584c.1
                                      have p584_1 := h584c.2.1
                                      have p584_2 := h584c.2.2.1
                                      have p584_3 := h584c.2.2.2
                                      linarith only [h0, h483, h521, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p584_1, u2ehi2]
                                    · have p584_0 := h584c.1
                                      have p584_1 := h584c.2.1
                                      have p584_2 := h584c.2.2.1
                                      have p584_3 := h584c.2.2.2
                                      linarith only [h508, hlam, p584_1]
                                    · have p584_0 := h584c.1
                                      have p584_1 := h584c.2.1
                                      have p584_2 := h584c.2.2.1
                                      have p584_3 := h584c.2.2.2
                                      linarith only [h0, h483, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p584_1]
                                    · have p584_0 := h584c.1
                                      have p584_1 := h584c.2.1
                                      have p584_2 := h584c.2.2.1
                                      have p584_3 := h584c.2.2.2
                                      linarith only [h483, hlam, p584_0]
                                    · have p584_0 := h584c.1
                                      have p584_1 := h584c.2.1
                                      have p584_2 := h584c.2.2.1
                                      have p584_3 := h584c.2.2.2
                                      linarith only [hlam, p584_0]
                                    · have p584_0 := h584c.1
                                      have p584_1 := h584c.2.1
                                      have p584_2 := h584c.2.2.1
                                      have p584_3 := h584c.2.2.2
                                      linarith only [h521, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p584_1, u2ehi2]
                                    · have p584_0 := h584c.1
                                      have p584_1 := h584c.2.1
                                      have p584_2 := h584c.2.2.1
                                      have p584_3 := h584c.2.2.2
                                      linarith only [h516, hlam, p584_1]
                                    · have p584_0 := h584c.1
                                      have p584_1 := h584c.2.1
                                      have p584_2 := h584c.2.2.1
                                      have p584_3 := h584c.2.2.2
                                      linarith only [h0, h483, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p584_1]
                                    · have p584_0 := h584c.1
                                      have p584_1 := h584c.2.1
                                      have p584_2 := h584c.2.2.1
                                      have p584_3 := h584c.2.2.2
                                      linarith only [h485, hlam, p584_1]
                                    · have p584_0 := h584c.1
                                      have p584_1 := h584c.2.1
                                      have p584_2 := h584c.2.2.1
                                      have p584_3 := h584c.2.2.2
                                      linarith only [h513, hlam, p584_1]
                                    · have p584_0 := h584c.1
                                      have p584_1 := h584c.2.1
                                      have p584_2 := h584c.2.2.1
                                      have p584_3 := h584c.2.2.2
                                      linarith only [hlam, p584_0]
                                    · have p584_0 := h584c.1
                                      have p584_1 := h584c.2.1
                                      have p584_2 := h584c.2.2.1
                                      have p584_3 := h584c.2.2.2
                                      linarith only [h521, hlam, p584_1]
                                    · have p584_0 := h584c.1
                                      have p584_1 := h584c.2.1
                                      have p584_2 := h584c.2.2.1
                                      have p584_3 := h584c.2.2.2
                                      linarith only [h0, h485, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p584_1]
                                    · have p584_0 := h584c.1
                                      have p584_1 := h584c.2.1
                                      have p584_2 := h584c.2.2.1
                                      have p584_3 := h584c.2.2.2
                                      linarith only [h485, h524, hc34, hlam, hphi, ht23, p584_1, u2ehi4]
                                    · have p584_0 := h584c.1
                                      have p584_1 := h584c.2.1
                                      have p584_2 := h584c.2.2.1
                                      have p584_3 := h584c.2.2.2
                                      linarith only [h513, h524, hc34, hlam, hphi, ht23, p584_1, u2ehi4]
                                    · have p584_0 := h584c.1
                                      have p584_1 := h584c.2.1
                                      have p584_2 := h584c.2.2.1
                                      have p584_3 := h584c.2.2.2
                                      linarith only [h524, hc34, hlam, hphi, ht23, p584_1, u2ehi4]
                                    · have p584_0 := h584c.1
                                      have p584_1 := h584c.2.1
                                      have p584_2 := h584c.2.2.1
                                      have p584_3 := h584c.2.2.2
                                      linarith only [hlam, p584_0]
                                    · have p584_0 := h584c.1
                                      have p584_1 := h584c.2.1
                                      have p584_2 := h584c.2.2.1
                                      have p584_3 := h584c.2.2.2
                                      rcases p584_3 (m.d 0 5) (by simp) with h604 | h604
                                      · linarith only [h508, h604, hlam]
                                      · linarith only [h510, h604, hlam]
                                    · have p584_0 := h584c.1
                                      have p584_1 := h584c.2.1
                                      have p584_2 := h584c.2.2.1
                                      have p584_3 := h584c.2.2.2
                                      linarith only [h510, hlam, p584_0]
                                    · have p584_0 := h584c.1
                                      have p584_1 := h584c.2.1
                                      have p584_2 := h584c.2.2.1
                                      have p584_3 := h584c.2.2.2
                                      linarith only [h518, hlam, p584_0]
                                    · have p584_0 := h584c.1
                                      have p584_1 := h584c.2.1
                                      have p584_2 := h584c.2.2.1
                                      have p584_3 := h584c.2.2.2
                                      linarith only [h523, hlam, p584_0]
                                    · have p584_0 := h584c.1
                                      have p584_1 := h584c.2.1
                                      have p584_2 := h584c.2.2.1
                                      have p584_3 := h584c.2.2.2
                                      linarith only [h524, hlam, p584_0]
                                    · have p584_0 := h584c.1
                                      have p584_1 := h584c.2.1
                                      have p584_2 := h584c.2.2.1
                                      have p584_3 := h584c.2.2.2
                                      linarith only [hlam, p584_0]
                                · linarith only [h482, h486, h511, h524, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                              · linarith only [h486, h510, h523, hc34, hlam, hphi, ht23, u2ehi3]
                        · linarith only [h486, h510, h512, h518, hc34, hlam, hphi, ht23, u2ehi3]
                  · linarith only [h0, h482, h511, h513, hc25, hlam, hphi, u2ehi2]
                · linarith only [h0, h482, h511, h512, hc24, hlam, hphi, u2ehi2]
              · linarith only [h0, h482, h511, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h618 | h618
              · rcases m.htr 1 2 4 (by decide) (by decide) with h619 | h619
                · rcases m.htr 1 2 5 (by decide) (by decide) with h620 | h620
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h621 | h621
                    · linarith only [h0, h482, h621, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h623 | h623
                      · linarith only [h0, h482, h508, h623, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                      · rcases m.htr 1 4 5 (by decide) (by decide) with h625 | h625
                        · linarith only [h482, h486, h510, h618, h621, h625, hc34, hlam, hphi, ht23, u2ehi2]
                        · rcases m.htr 2 3 4 (by decide) (by decide) with h627 | h627
                          · linarith only [h0, h482, h618, h627, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                          · rcases m.htr 2 3 5 (by decide) (by decide) with h629 | h629
                            · linarith only [h0, h483, h618, h621, h625, h629, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi4]
                            · rcases m.htr 2 4 5 (by decide) (by decide) with h631 | h631
                              · linarith only [h0, h483, h486, h510, h619, h625, h631, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi0]
                              · rcases m.htr 3 4 5 (by decide) (by decide) with h633 | h633
                                · linarith only [h482, h486, h510, h618, h633, hc34, hlam, hphi, ht23, u2ehi2]
                                · linarith only [h482, h486, h618, h633, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                  · linarith only [h0, h482, h618, h620, hc25, hlam, hphi, u2ehi2]
                · linarith only [h0, h482, h618, h619, hc24, hlam, hphi, u2ehi2]
              · linarith only [h0, h482, h618, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
      · linarith only [h484, h485, hc25, hlam, hphi, u2ehi2]
    · linarith only [h0, h482, h484, hlam]
  · rcases m.htr 0 2 3 (by decide) (by decide) with h641 | h641
    · rcases m.htr 0 2 5 (by decide) (by decide) with h642 | h642
      · rcases m.htr 0 3 4 (by decide) (by decide) with h643 | h643
        · rcases m.htr 0 3 5 (by decide) (by decide) with h644 | h644
          · linarith only [h482, h483, h644, hlam]
          · linarith only [h643, h644, hc35, hlam, hphi, u3ehi3]
        · rcases m.htr 0 3 5 (by decide) (by decide) with h647 | h647
          · linarith only [h643, h647, hc34, hlam, hphi, u3ehi4]
          · rcases m.htr 0 4 5 (by decide) (by decide) with h649 | h649
            · rcases m.htr 1 2 3 (by decide) (by decide) with h650 | h650
              · rcases m.htr 1 2 4 (by decide) (by decide) with h651 | h651
                · rcases m.htr 1 2 5 (by decide) (by decide) with h652 | h652
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h653 | h653
                    · linarith only [h482, h643, h653, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h655 | h655
                      · linarith only [h482, h483, h652, h655, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi4]
                      · linarith only [h482, h483, h650, h655, hc35, hlam, hphi, ht23, u2ehi2]
                  · linarith only [h0, h642, h652, hlam]
                · linarith only [h0, h642, h651, hc24, hlam, hphi, u2ehi4]
              · linarith only [h0, h482, h641, h650, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
            · rcases m.htr 1 2 3 (by decide) (by decide) with h661 | h661
              · rcases m.htr 1 2 4 (by decide) (by decide) with h662 | h662
                · rcases m.htr 1 2 5 (by decide) (by decide) with h663 | h663
                  · rcases m.htr 1 3 4 (by decide) (by decide) with h664 | h664
                    · linarith only [h482, h483, h663, h664, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                    · rcases m.htr 1 3 5 (by decide) (by decide) with h666 | h666
                      · linarith only [h482, h483, h663, h666, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi4]
                      · linarith only [h482, h483, h661, h666, hc35, hlam, hphi, ht23, u2ehi2]
                  · linarith only [h0, h642, h663, hlam]
                · linarith only [h0, h642, h662, hc24, hlam, hphi, u2ehi4]
              · linarith only [h0, h482, h661, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
      · linarith only [h641, h642, hc25, hlam, hphi, u2ehi2]
    · linarith only [h0, h482, h641, hlam]

set_option maxHeartbeats 4664000 in
theorem r1l7_10_12_13_25_L_I_L_R_L_R_H_I_x1_x1_x0 (m : N7Model)
    (hb0 : CMSig1_7_L_I m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_H_I m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
    (h0 : (m.d 1 2 + m.lam ≤ m.d 0 1 ∧ m.d 1 2 < m.d 0 2 ∧ m.d 0 2 < m.d 0 1))
    (h482 : (m.d 1 3 + m.lam ≤ m.d 0 1 ∧ m.d 1 3 < m.d 0 3 ∧ m.d 0 3 < m.d 0 1))
    (h674 : (m.d 0 1 + m.lam ≤ m.d 1 5 ∧ m.d 0 1 < m.d 0 5 ∧ m.d 0 5 < m.d 1 5))
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
  have h0emax := hb0.2.2
  have h2ehi := hb2.1
  have h3ehi := hb3.1
  have h5bigk := hb5.1
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u2ehi4 := h2ehi (m.d 2 5) (by simp)
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h675 | h675
  · rcases m.htr 0 2 5 (by decide) (by decide) with h676 | h676
    · rcases m.htr 0 3 4 (by decide) (by decide) with h677 | h677
      · rcases m.htr 0 3 5 (by decide) (by decide) with h678 | h678
        · rcases m.htr 0 4 5 (by decide) (by decide) with h679 | h679
          · rcases m.htr 1 2 3 (by decide) (by decide) with h680 | h680
            · rcases m.htr 1 2 4 (by decide) (by decide) with h681 | h681
              · rcases m.htr 1 2 5 (by decide) (by decide) with h682 | h682
                · rcases m.htr 1 3 4 (by decide) (by decide) with h683 | h683
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h684 | h684
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h685 | h685
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h686 | h686
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h687 | h687
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h688 | h688
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h689 | h689
                              · rcases h0emax with h690 | h690 | h690 | h690 | h690
                                · linarith only [h674, h682, h690, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi4]
                                · linarith only [h675, h686, h689, h690, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi4]
                                · linarith only [h482, h674, h682, h690, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi4]
                                · rcases h5bigk with h694c | h694c | h694c | h694c | h694c | h694c | h694c | h694c | h694c | h694c | h694c | h694c | h694c | h694c | h694c | h694c | h694c | h694c | h694c | h694c | h694c | h694c | h694c | h694c | h694c
                                  · have p694_0 := h694c.1
                                    have p694_1 := h694c.2.1
                                    have p694_2 := h694c.2.2.1
                                    have p694_3 := h694c.2.2.2
                                    linarith only [hlam, p694_0]
                                  · have p694_0 := h694c.1
                                    have p694_1 := h694c.2.1
                                    have p694_2 := h694c.2.2.1
                                    have p694_3 := h694c.2.2.2
                                    linarith only [h679, h682, h690, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p694_1, u2ehi4]
                                  · have p694_0 := h694c.1
                                    have p694_1 := h694c.2.1
                                    have p694_2 := h694c.2.2.1
                                    have p694_3 := h694c.2.2.2
                                    linarith only [h679, h690, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p694_1, u2ehi4]
                                  · have p694_0 := h694c.1
                                    have p694_1 := h694c.2.1
                                    have p694_2 := h694c.2.2.1
                                    have p694_3 := h694c.2.2.2
                                    linarith only [h679, h690, hlam, hphi, ht0b, ht34, ht45, ht5b, p694_1, u3ehi4]
                                  · have p694_0 := h694c.1
                                    have p694_1 := h694c.2.1
                                    have p694_2 := h694c.2.2.1
                                    have p694_3 := h694c.2.2.2
                                    linarith only [h679, h690, hc45, hlam, hphi, ht0b, ht5b, p694_1]
                                  · have p694_0 := h694c.1
                                    have p694_1 := h694c.2.1
                                    have p694_2 := h694c.2.2.1
                                    have p694_3 := h694c.2.2.2
                                    linarith only [h674, hlam, p694_0]
                                  · have p694_0 := h694c.1
                                    have p694_1 := h694c.2.1
                                    have p694_2 := h694c.2.2.1
                                    have p694_3 := h694c.2.2.2
                                    linarith only [hlam, p694_0]
                                  · have p694_0 := h694c.1
                                    have p694_1 := h694c.2.1
                                    have p694_2 := h694c.2.2.1
                                    have p694_3 := h694c.2.2.2
                                    linarith only [h674, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p694_1, u2ehi4]
                                  · have p694_0 := h694c.1
                                    have p694_1 := h694c.2.1
                                    have p694_2 := h694c.2.2.1
                                    have p694_3 := h694c.2.2.2
                                    linarith only [h482, h674, h680, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p694_1, u3ehi4]
                                  · have p694_0 := h694c.1
                                    have p694_1 := h694c.2.1
                                    have p694_2 := h694c.2.2.1
                                    have p694_3 := h694c.2.2.2
                                    linarith only [h482, h674, h680, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p694_1]
                                  · have p694_0 := h694c.1
                                    have p694_1 := h694c.2.1
                                    have p694_2 := h694c.2.2.1
                                    have p694_3 := h694c.2.2.2
                                    linarith only [h676, hlam, p694_1]
                                  · have p694_0 := h694c.1
                                    have p694_1 := h694c.2.1
                                    have p694_2 := h694c.2.2.1
                                    have p694_3 := h694c.2.2.2
                                    linarith only [h682, hlam, p694_1]
                                  · have p694_0 := h694c.1
                                    have p694_1 := h694c.2.1
                                    have p694_2 := h694c.2.2.1
                                    have p694_3 := h694c.2.2.2
                                    linarith only [hlam, p694_0]
                                  · have p694_0 := h694c.1
                                    have p694_1 := h694c.2.1
                                    have p694_2 := h694c.2.2.1
                                    have p694_3 := h694c.2.2.2
                                    linarith only [hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p694_1, u3ehi4]
                                  · have p694_0 := h694c.1
                                    have p694_1 := h694c.2.1
                                    have p694_2 := h694c.2.2.1
                                    have p694_3 := h694c.2.2.2
                                    linarith only [h482, h674, h680, h682, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p694_1]
                                  · have p694_0 := h694c.1
                                    have p694_1 := h694c.2.1
                                    have p694_2 := h694c.2.2.1
                                    have p694_3 := h694c.2.2.2
                                    linarith only [h678, hlam, p694_0]
                                  · have p694_0 := h694c.1
                                    have p694_1 := h694c.2.1
                                    have p694_2 := h694c.2.2.1
                                    have p694_3 := h694c.2.2.2
                                    linarith only [h684, hlam, p694_0]
                                  · have p694_0 := h694c.1
                                    have p694_1 := h694c.2.1
                                    have p694_2 := h694c.2.2.1
                                    have p694_3 := h694c.2.2.2
                                    linarith only [h687, hlam, p694_0]
                                  · have p694_0 := h694c.1
                                    have p694_1 := h694c.2.1
                                    have p694_2 := h694c.2.2.1
                                    have p694_3 := h694c.2.2.2
                                    linarith only [hlam, p694_0]
                                  · have p694_0 := h694c.1
                                    have p694_1 := h694c.2.1
                                    have p694_2 := h694c.2.2.1
                                    have p694_3 := h694c.2.2.2
                                    linarith only [h482, h674, h680, h682, h686, h689, hc12, hc23, hc45, hlam, hphi, ht01, ht0b, ht5b, p694_1, u2ehi4]
                                  · have p694_0 := h694c.1
                                    have p694_1 := h694c.2.1
                                    have p694_2 := h694c.2.2.1
                                    have p694_3 := h694c.2.2.2
                                    linarith only [h679, hlam, p694_0]
                                  · have p694_0 := h694c.1
                                    have p694_1 := h694c.2.1
                                    have p694_2 := h694c.2.2.1
                                    have p694_3 := h694c.2.2.2
                                    linarith only [h685, hlam, p694_0]
                                  · have p694_0 := h694c.1
                                    have p694_1 := h694c.2.1
                                    have p694_2 := h694c.2.2.1
                                    have p694_3 := h694c.2.2.2
                                    linarith only [h688, hlam, p694_0]
                                  · have p694_0 := h694c.1
                                    have p694_1 := h694c.2.1
                                    have p694_2 := h694c.2.2.1
                                    have p694_3 := h694c.2.2.2
                                    linarith only [h689, hlam, p694_0]
                                  · have p694_0 := h694c.1
                                    have p694_1 := h694c.2.1
                                    have p694_2 := h694c.2.2.1
                                    have p694_3 := h694c.2.2.2
                                    linarith only [hlam, p694_0]
                                · rcases h5bigk with h720c | h720c | h720c | h720c | h720c | h720c | h720c | h720c | h720c | h720c | h720c | h720c | h720c | h720c | h720c | h720c | h720c | h720c | h720c | h720c | h720c | h720c | h720c | h720c | h720c
                                  · have p720_0 := h720c.1
                                    have p720_1 := h720c.2.1
                                    have p720_2 := h720c.2.2.1
                                    have p720_3 := h720c.2.2.2
                                    linarith only [hlam, p720_0]
                                  · have p720_0 := h720c.1
                                    have p720_1 := h720c.2.1
                                    have p720_2 := h720c.2.2.1
                                    have p720_3 := h720c.2.2.2
                                    linarith only [h679, h682, hc04, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p720_1, u2ehi4]
                                  · have p720_0 := h720c.1
                                    have p720_1 := h720c.2.1
                                    have p720_2 := h720c.2.2.1
                                    have p720_3 := h720c.2.2.2
                                    linarith only [h482, h674, h680, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p720_1, u2ehi4]
                                  · have p720_0 := h720c.1
                                    have p720_1 := h720c.2.1
                                    have p720_2 := h720c.2.2.1
                                    have p720_3 := h720c.2.2.2
                                    linarith only [h482, h674, h680, hc12, hc35, hlam, hphi, ht01, ht0b, ht5b, p720_1]
                                  · have p720_0 := h720c.1
                                    have p720_1 := h720c.2.1
                                    have p720_2 := h720c.2.2.1
                                    have p720_3 := h720c.2.2.2
                                    linarith only [h482, h674, h680, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p720_1]
                                  · have p720_0 := h720c.1
                                    have p720_1 := h720c.2.1
                                    have p720_2 := h720c.2.2.1
                                    have p720_3 := h720c.2.2.2
                                    linarith only [h674, hlam, p720_0]
                                  · have p720_0 := h720c.1
                                    have p720_1 := h720c.2.1
                                    have p720_2 := h720c.2.2.1
                                    have p720_3 := h720c.2.2.2
                                    linarith only [hlam, p720_0]
                                  · have p720_0 := h720c.1
                                    have p720_1 := h720c.2.1
                                    have p720_2 := h720c.2.2.1
                                    have p720_3 := h720c.2.2.2
                                    linarith only [hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p720_1, u2ehi4]
                                  · have p720_0 := h720c.1
                                    have p720_1 := h720c.2.1
                                    have p720_2 := h720c.2.2.1
                                    have p720_3 := h720c.2.2.2
                                    linarith only [h482, h674, h680, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p720_1, u3ehi4]
                                  · have p720_0 := h720c.1
                                    have p720_1 := h720c.2.1
                                    have p720_2 := h720c.2.2.1
                                    have p720_3 := h720c.2.2.2
                                    linarith only [h482, h674, h680, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p720_1]
                                  · have p720_0 := h720c.1
                                    have p720_1 := h720c.2.1
                                    have p720_2 := h720c.2.2.1
                                    have p720_3 := h720c.2.2.2
                                    linarith only [h676, hlam, p720_1]
                                  · have p720_0 := h720c.1
                                    have p720_1 := h720c.2.1
                                    have p720_2 := h720c.2.2.1
                                    have p720_3 := h720c.2.2.2
                                    linarith only [h682, hlam, p720_1]
                                  · have p720_0 := h720c.1
                                    have p720_1 := h720c.2.1
                                    have p720_2 := h720c.2.2.1
                                    have p720_3 := h720c.2.2.2
                                    linarith only [hlam, p720_0]
                                  · have p720_0 := h720c.1
                                    have p720_1 := h720c.2.1
                                    have p720_2 := h720c.2.2.1
                                    have p720_3 := h720c.2.2.2
                                    linarith only [hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p720_1, u3ehi4]
                                  · have p720_0 := h720c.1
                                    have p720_1 := h720c.2.1
                                    have p720_2 := h720c.2.2.1
                                    have p720_3 := h720c.2.2.2
                                    linarith only [h482, h674, h680, h682, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p720_1]
                                  · have p720_0 := h720c.1
                                    have p720_1 := h720c.2.1
                                    have p720_2 := h720c.2.2.1
                                    have p720_3 := h720c.2.2.2
                                    linarith only [h678, hlam, p720_0]
                                  · have p720_0 := h720c.1
                                    have p720_1 := h720c.2.1
                                    have p720_2 := h720c.2.2.1
                                    have p720_3 := h720c.2.2.2
                                    linarith only [h684, hlam, p720_0]
                                  · have p720_0 := h720c.1
                                    have p720_1 := h720c.2.1
                                    have p720_2 := h720c.2.2.1
                                    have p720_3 := h720c.2.2.2
                                    linarith only [h687, hlam, p720_0]
                                  · have p720_0 := h720c.1
                                    have p720_1 := h720c.2.1
                                    have p720_2 := h720c.2.2.1
                                    have p720_3 := h720c.2.2.2
                                    linarith only [hlam, p720_0]
                                  · have p720_0 := h720c.1
                                    have p720_1 := h720c.2.1
                                    have p720_2 := h720c.2.2.1
                                    have p720_3 := h720c.2.2.2
                                    linarith only [h482, h678, h680, hc12, hc45, hlam, hphi, ht01, ht0b, ht5b, p720_1]
                                  · have p720_0 := h720c.1
                                    have p720_1 := h720c.2.1
                                    have p720_2 := h720c.2.2.1
                                    have p720_3 := h720c.2.2.2
                                    linarith only [h679, hlam, p720_0]
                                  · have p720_0 := h720c.1
                                    have p720_1 := h720c.2.1
                                    have p720_2 := h720c.2.2.1
                                    have p720_3 := h720c.2.2.2
                                    linarith only [h685, hlam, p720_0]
                                  · have p720_0 := h720c.1
                                    have p720_1 := h720c.2.1
                                    have p720_2 := h720c.2.2.1
                                    have p720_3 := h720c.2.2.2
                                    linarith only [h688, hlam, p720_0]
                                  · have p720_0 := h720c.1
                                    have p720_1 := h720c.2.1
                                    have p720_2 := h720c.2.2.1
                                    have p720_3 := h720c.2.2.2
                                    linarith only [h689, hlam, p720_0]
                                  · have p720_0 := h720c.1
                                    have p720_1 := h720c.2.1
                                    have p720_2 := h720c.2.2.1
                                    have p720_3 := h720c.2.2.2
                                    linarith only [hlam, p720_0]
                              · linarith only [h482, h674, h680, h685, h689, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                            · linarith only [h482, h674, h680, h685, h688, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                          · linarith only [h482, h674, h680, h684, h687, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h749 | h749
                          · linarith only [h686, h749, hc34, hlam, hphi, u3ehi4]
                          · linarith only [h482, h674, h680, h684, h749, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h752 | h752
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h753 | h753
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h754 | h754
                            · linarith only [h681, h685, h754, hlam]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h756 | h756
                              · linarith only [h681, h685, h752, h756, hlam]
                              · rcases h0emax with h758 | h758 | h758 | h758 | h758
                                · linarith only [h674, h682, h758, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi4]
                                · linarith only [h0, h674, h679, h681, h685, h758, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                                · linarith only [h677, h679, h681, h685, h758, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                                · linarith only [h679, h681, h685, h758, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                                · linarith only [h679, h681, h685, h758, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                          · linarith only [h482, h674, h680, h684, h753, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                        · linarith only [h675, h677, h679, h683, h685, h752, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                    · linarith only [h482, h674, h676, h684, hc35, hlam, hphi, ht23, u2ehi4]
                  · linarith only [h482, h674, h675, h677, h682, h683, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi4]
                · linarith only [h0, h674, h676, h682, hlam]
              · linarith only [h0, h676, h681, hc24, hlam, hphi, u2ehi4]
            · linarith only [h0, h674, h676, h680, hc23, hlam, hphi, u2ehi4]
          · rcases m.htr 1 2 3 (by decide) (by decide) with h771 | h771
            · rcases m.htr 1 2 4 (by decide) (by decide) with h772 | h772
              · rcases m.htr 1 2 5 (by decide) (by decide) with h773 | h773
                · rcases m.htr 1 3 4 (by decide) (by decide) with h774 | h774
                  · rcases m.htr 1 3 5 (by decide) (by decide) with h775 | h775
                    · rcases m.htr 1 4 5 (by decide) (by decide) with h776 | h776
                      · linarith only [h482, h674, h677, h679, h771, h776, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                      · rcases m.htr 2 3 4 (by decide) (by decide) with h778 | h778
                        · rcases m.htr 2 3 5 (by decide) (by decide) with h779 | h779
                          · rcases m.htr 2 4 5 (by decide) (by decide) with h780 | h780
                            · linarith only [h482, h674, h677, h679, h771, h772, h776, h780, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                            · rcases m.htr 3 4 5 (by decide) (by decide) with h782 | h782
                              · linarith only [h675, h772, h776, h778, h782, hc02, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                              · rcases h0emax with h784 | h784 | h784 | h784 | h784
                                · linarith only [h674, h773, h784, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi4]
                                · linarith only [h675, h784, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                                · linarith only [h482, h674, h772, h776, h784, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                                · rcases h5bigk with h788c | h788c | h788c | h788c | h788c | h788c | h788c | h788c | h788c | h788c | h788c | h788c | h788c | h788c | h788c | h788c | h788c | h788c | h788c | h788c | h788c | h788c | h788c | h788c | h788c
                                  · have p788_0 := h788c.1
                                    have p788_1 := h788c.2.1
                                    have p788_2 := h788c.2.2.1
                                    have p788_3 := h788c.2.2.2
                                    linarith only [hlam, p788_0]
                                  · have p788_0 := h788c.1
                                    have p788_1 := h788c.2.1
                                    have p788_2 := h788c.2.2.1
                                    have p788_3 := h788c.2.2.2
                                    linarith only [h772, h776, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p788_1, u2ehi3]
                                  · have p788_0 := h788c.1
                                    have p788_1 := h788c.2.1
                                    have p788_2 := h788c.2.2.1
                                    have p788_3 := h788c.2.2.2
                                    linarith only [h674, h780, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p788_1, u2ehi3]
                                  · have p788_0 := h788c.1
                                    have p788_1 := h788c.2.1
                                    have p788_2 := h788c.2.2.1
                                    have p788_3 := h788c.2.2.2
                                    linarith only [h482, h674, h771, h782, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p788_1, u3ehi3]
                                  · have p788_0 := h788c.1
                                    have p788_1 := h788c.2.1
                                    have p788_2 := h788c.2.2.1
                                    have p788_3 := h788c.2.2.2
                                    linarith only [h679, hlam, p788_1]
                                  · have p788_0 := h788c.1
                                    have p788_1 := h788c.2.1
                                    have p788_2 := h788c.2.2.1
                                    have p788_3 := h788c.2.2.2
                                    linarith only [h674, hlam, p788_0]
                                  · have p788_0 := h788c.1
                                    have p788_1 := h788c.2.1
                                    have p788_2 := h788c.2.2.1
                                    have p788_3 := h788c.2.2.2
                                    linarith only [hlam, p788_0]
                                  · have p788_0 := h788c.1
                                    have p788_1 := h788c.2.1
                                    have p788_2 := h788c.2.2.1
                                    have p788_3 := h788c.2.2.2
                                    linarith only [h780, hc15, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p788_1, u2ehi3]
                                  · have p788_0 := h788c.1
                                    have p788_1 := h788c.2.1
                                    have p788_2 := h788c.2.2.1
                                    have p788_3 := h788c.2.2.2
                                    linarith only [h482, h674, h771, h782, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p788_1, u3ehi3]
                                  · have p788_0 := h788c.1
                                    have p788_1 := h788c.2.1
                                    have p788_2 := h788c.2.2.1
                                    have p788_3 := h788c.2.2.2
                                    linarith only [h776, hlam, p788_1]
                                  · have p788_0 := h788c.1
                                    have p788_1 := h788c.2.1
                                    have p788_2 := h788c.2.2.1
                                    have p788_3 := h788c.2.2.2
                                    linarith only [h676, hlam, p788_1]
                                  · have p788_0 := h788c.1
                                    have p788_1 := h788c.2.1
                                    have p788_2 := h788c.2.2.1
                                    have p788_3 := h788c.2.2.2
                                    linarith only [h773, hlam, p788_1]
                                  · have p788_0 := h788c.1
                                    have p788_1 := h788c.2.1
                                    have p788_2 := h788c.2.2.1
                                    have p788_3 := h788c.2.2.2
                                    linarith only [hlam, p788_0]
                                  · have p788_0 := h788c.1
                                    have p788_1 := h788c.2.1
                                    have p788_2 := h788c.2.2.1
                                    have p788_3 := h788c.2.2.2
                                    linarith only [h782, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p788_1, u3ehi3]
                                  · have p788_0 := h788c.1
                                    have p788_1 := h788c.2.1
                                    have p788_2 := h788c.2.2.1
                                    have p788_3 := h788c.2.2.2
                                    linarith only [h780, hlam, p788_1]
                                  · have p788_0 := h788c.1
                                    have p788_1 := h788c.2.1
                                    have p788_2 := h788c.2.2.1
                                    have p788_3 := h788c.2.2.2
                                    linarith only [h678, hlam, p788_0]
                                  · have p788_0 := h788c.1
                                    have p788_1 := h788c.2.1
                                    have p788_2 := h788c.2.2.1
                                    have p788_3 := h788c.2.2.2
                                    linarith only [h775, hlam, p788_0]
                                  · have p788_0 := h788c.1
                                    have p788_1 := h788c.2.1
                                    have p788_2 := h788c.2.2.1
                                    have p788_3 := h788c.2.2.2
                                    linarith only [h779, hlam, p788_0]
                                  · have p788_0 := h788c.1
                                    have p788_1 := h788c.2.1
                                    have p788_2 := h788c.2.2.1
                                    have p788_3 := h788c.2.2.2
                                    linarith only [hlam, p788_0]
                                  · have p788_0 := h788c.1
                                    have p788_1 := h788c.2.1
                                    have p788_2 := h788c.2.2.1
                                    have p788_3 := h788c.2.2.2
                                    linarith only [h782, hlam, p788_1]
                                  · have p788_0 := h788c.1
                                    have p788_1 := h788c.2.1
                                    have p788_2 := h788c.2.2.1
                                    have p788_3 := h788c.2.2.2
                                    linarith only [h676, hc45, hlam, hphi, ht23, ht34, p788_1, u2ehi4]
                                  · have p788_0 := h788c.1
                                    have p788_1 := h788c.2.1
                                    have p788_2 := h788c.2.2.1
                                    have p788_3 := h788c.2.2.2
                                    linarith only [h773, hc45, hlam, hphi, ht23, ht34, p788_1, u2ehi4]
                                  · have p788_0 := h788c.1
                                    have p788_1 := h788c.2.1
                                    have p788_2 := h788c.2.2.1
                                    have p788_3 := h788c.2.2.2
                                    linarith only [h779, h782, hc45, hlam, hphi, ht34, p788_1, u3ehi3]
                                  · have p788_0 := h788c.1
                                    have p788_1 := h788c.2.1
                                    have p788_2 := h788c.2.2.1
                                    have p788_3 := h788c.2.2.2
                                    linarith only [h782, hc45, hlam, hphi, ht34, p788_1, u3ehi3]
                                  · have p788_0 := h788c.1
                                    have p788_1 := h788c.2.1
                                    have p788_2 := h788c.2.2.1
                                    have p788_3 := h788c.2.2.2
                                    linarith only [hlam, p788_0]
                                · rcases h5bigk with h814c | h814c | h814c | h814c | h814c | h814c | h814c | h814c | h814c | h814c | h814c | h814c | h814c | h814c | h814c | h814c | h814c | h814c | h814c | h814c | h814c | h814c | h814c | h814c | h814c
                                  · have p814_0 := h814c.1
                                    have p814_1 := h814c.2.1
                                    have p814_2 := h814c.2.2.1
                                    have p814_3 := h814c.2.2.2
                                    linarith only [hlam, p814_0]
                                  · have p814_0 := h814c.1
                                    have p814_1 := h814c.2.1
                                    have p814_2 := h814c.2.2.1
                                    have p814_3 := h814c.2.2.2
                                    linarith only [h772, h776, hc05, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p814_1, u2ehi3]
                                  · have p814_0 := h814c.1
                                    have p814_1 := h814c.2.1
                                    have p814_2 := h814c.2.2.1
                                    have p814_3 := h814c.2.2.2
                                    linarith only [h482, h674, h771, h779, h782, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p814_1, u3ehi3]
                                  · have p814_0 := h814c.1
                                    have p814_1 := h814c.2.1
                                    have p814_2 := h814c.2.2.1
                                    have p814_3 := h814c.2.2.2
                                    linarith only [h482, h674, h771, h782, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p814_1, u3ehi3]
                                  · have p814_0 := h814c.1
                                    have p814_1 := h814c.2.1
                                    have p814_2 := h814c.2.2.1
                                    have p814_3 := h814c.2.2.2
                                    linarith only [h679, hlam, p814_1]
                                  · have p814_0 := h814c.1
                                    have p814_1 := h814c.2.1
                                    have p814_2 := h814c.2.2.1
                                    have p814_3 := h814c.2.2.2
                                    linarith only [h674, hlam, p814_0]
                                  · have p814_0 := h814c.1
                                    have p814_1 := h814c.2.1
                                    have p814_2 := h814c.2.2.1
                                    have p814_3 := h814c.2.2.2
                                    linarith only [hlam, p814_0]
                                  · have p814_0 := h814c.1
                                    have p814_1 := h814c.2.1
                                    have p814_2 := h814c.2.2.1
                                    have p814_3 := h814c.2.2.2
                                    linarith only [h779, h782, hc15, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p814_1, u3ehi3]
                                  · have p814_0 := h814c.1
                                    have p814_1 := h814c.2.1
                                    have p814_2 := h814c.2.2.1
                                    have p814_3 := h814c.2.2.2
                                    linarith only [h482, h674, h771, h782, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p814_1, u3ehi3]
                                  · have p814_0 := h814c.1
                                    have p814_1 := h814c.2.1
                                    have p814_2 := h814c.2.2.1
                                    have p814_3 := h814c.2.2.2
                                    linarith only [h776, hlam, p814_1]
                                  · have p814_0 := h814c.1
                                    have p814_1 := h814c.2.1
                                    have p814_2 := h814c.2.2.1
                                    have p814_3 := h814c.2.2.2
                                    linarith only [h676, hlam, p814_1]
                                  · have p814_0 := h814c.1
                                    have p814_1 := h814c.2.1
                                    have p814_2 := h814c.2.2.1
                                    have p814_3 := h814c.2.2.2
                                    linarith only [h773, hlam, p814_1]
                                  · have p814_0 := h814c.1
                                    have p814_1 := h814c.2.1
                                    have p814_2 := h814c.2.2.1
                                    have p814_3 := h814c.2.2.2
                                    linarith only [hlam, p814_0]
                                  · have p814_0 := h814c.1
                                    have p814_1 := h814c.2.1
                                    have p814_2 := h814c.2.2.1
                                    have p814_3 := h814c.2.2.2
                                    linarith only [h782, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p814_1, u3ehi3]
                                  · have p814_0 := h814c.1
                                    have p814_1 := h814c.2.1
                                    have p814_2 := h814c.2.2.1
                                    have p814_3 := h814c.2.2.2
                                    linarith only [h780, hlam, p814_1]
                                  · have p814_0 := h814c.1
                                    have p814_1 := h814c.2.1
                                    have p814_2 := h814c.2.2.1
                                    have p814_3 := h814c.2.2.2
                                    linarith only [h678, hlam, p814_0]
                                  · have p814_0 := h814c.1
                                    have p814_1 := h814c.2.1
                                    have p814_2 := h814c.2.2.1
                                    have p814_3 := h814c.2.2.2
                                    linarith only [h775, hlam, p814_0]
                                  · have p814_0 := h814c.1
                                    have p814_1 := h814c.2.1
                                    have p814_2 := h814c.2.2.1
                                    have p814_3 := h814c.2.2.2
                                    linarith only [h779, hlam, p814_0]
                                  · have p814_0 := h814c.1
                                    have p814_1 := h814c.2.1
                                    have p814_2 := h814c.2.2.1
                                    have p814_3 := h814c.2.2.2
                                    linarith only [hlam, p814_0]
                                  · have p814_0 := h814c.1
                                    have p814_1 := h814c.2.1
                                    have p814_2 := h814c.2.2.1
                                    have p814_3 := h814c.2.2.2
                                    linarith only [h782, hlam, p814_1]
                                  · have p814_0 := h814c.1
                                    have p814_1 := h814c.2.1
                                    have p814_2 := h814c.2.2.1
                                    have p814_3 := h814c.2.2.2
                                    linarith only [h676, hc45, hlam, hphi, ht23, ht34, p814_1, u2ehi4]
                                  · have p814_0 := h814c.1
                                    have p814_1 := h814c.2.1
                                    have p814_2 := h814c.2.2.1
                                    have p814_3 := h814c.2.2.2
                                    linarith only [h773, hc45, hlam, hphi, ht23, ht34, p814_1, u2ehi4]
                                  · have p814_0 := h814c.1
                                    have p814_1 := h814c.2.1
                                    have p814_2 := h814c.2.2.1
                                    have p814_3 := h814c.2.2.2
                                    linarith only [h779, h782, hc45, hlam, hphi, ht34, p814_1, u3ehi3]
                                  · have p814_0 := h814c.1
                                    have p814_1 := h814c.2.1
                                    have p814_2 := h814c.2.2.1
                                    have p814_3 := h814c.2.2.2
                                    linarith only [h782, hc45, hlam, hphi, ht34, p814_1, u3ehi3]
                                  · have p814_0 := h814c.1
                                    have p814_1 := h814c.2.1
                                    have p814_2 := h814c.2.2.1
                                    have p814_3 := h814c.2.2.2
                                    linarith only [hlam, p814_0]
                          · linarith only [h482, h674, h771, h775, h779, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi2]
                        · linarith only [h677, h679, h778, hc45, hlam, hphi, ht23, ht34, u2ehi2]
                    · linarith only [h482, h674, h676, h775, hc35, hlam, hphi, ht23, u2ehi4]
                  · linarith only [h482, h674, h677, h679, h773, h774, hc45, hlam, hphi, ht23, ht34, u2ehi4]
                · linarith only [h0, h675, h773, hc25, hlam, hphi, u2ehi2]
              · linarith only [h482, h674, h676, h771, h772, hc24, hlam, hphi, u2ehi4]
            · linarith only [h0, h675, h771, hlam]
        · linarith only [h677, h678, hc35, hlam, hphi, u3ehi3]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h848 | h848
        · linarith only [h677, h848, hc34, hlam, hphi, u3ehi4]
        · linarith only [h482, h674, h848, hlam]
    · linarith only [h675, h676, hc25, hlam, hphi, u2ehi2]
  · rcases m.htr 0 2 5 (by decide) (by decide) with h852 | h852
    · linarith only [h675, h852, hc23, hlam, hphi, u2ehi4]
    · linarith only [h0, h674, h852, hlam]

end R2N4
