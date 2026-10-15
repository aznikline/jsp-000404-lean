import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_22_13_H_I_L_R_x0 (m : N7Model)
    (hb2 : CMSig2_7_H_I m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_R m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (h0 : (m.d 0 1 + m.lam ≤ m.d 1 2 ∧ m.d 0 1 < m.d 0 2 ∧ m.d 0 2 < m.d 1 2))
    : False := by
  have hlam := m.hlam
  obtain ⟨hplo, hphi⟩ := m.hp
  have ht0b := m.ht0
  have ht5b := m.ht5
  have hc01 := m.hcor 0 1 (by decide)
  have hc02 := m.hcor 0 2 (by decide)
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
  have h2bigk := hb2.1
  have h3ehi := hb3.1
  have u3ehi0 := h3ehi (m.d 0 3) (by simp)
  have u3ehi1 := h3ehi (m.d 1 3) (by simp)
  have u3ehi2 := h3ehi (m.d 2 3) (by simp)
  have u3ehi3 := h3ehi (m.d 3 4) (by simp)
  have u3ehi4 := h3ehi (m.d 3 5) (by simp)
  rcases m.htr 0 2 3 (by decide) (by decide) with h1 | h1
  · rcases m.htr 0 2 4 (by decide) (by decide) with h2 | h2
    · rcases m.htr 0 2 5 (by decide) (by decide) with h3 | h3
      · rcases m.htr 1 2 3 (by decide) (by decide) with h4 | h4
        · rcases m.htr 1 2 4 (by decide) (by decide) with h5 | h5
          · rcases m.htr 1 2 5 (by decide) (by decide) with h6 | h6
            · rcases m.htr 1 3 4 (by decide) (by decide) with h7 | h7
              · rcases m.htr 1 3 5 (by decide) (by decide) with h8 | h8
                · rcases m.htr 1 4 5 (by decide) (by decide) with h9 | h9
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h10 | h10
                    · linarith only [h0, h10, h4, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                    · linarith only [h0, h10, h4, h7, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h13 | h13
                    · linarith only [h0, h13, h4, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                    · linarith only [h0, h13, h4, h7, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                · linarith only [h7, h8, hc35, hlam, hphi, u3ehi3]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h17 | h17
                · linarith only [h17, h7, hc34, hlam, hphi, u3ehi4]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h19 | h19
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h20 | h20
                    · linarith only [h0, h1, h20, h7, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h22 | h22
                      · linarith only [h17, h22, h4, hlam]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h24 | h24
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h25 | h25
                          · rcases h2bigk with h26c | h26c | h26c | h26c | h26c | h26c | h26c | h26c | h26c | h26c | h26c | h26c | h26c | h26c | h26c | h26c | h26c | h26c | h26c | h26c | h26c | h26c | h26c | h26c | h26c
                            · have p26_0 := h26c.1
                              have p26_1 := h26c.2.1
                              have p26_2 := h26c.2.2.1
                              have p26_3 := h26c.2.2.2
                              linarith only [hlam, p26_0]
                            · have p26_0 := h26c.1
                              have p26_1 := h26c.2.1
                              have p26_2 := h26c.2.2.1
                              have p26_3 := h26c.2.2.2
                              linarith only [h0, h4, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p26_1, u3ehi2]
                            · have p26_0 := h26c.1
                              have p26_1 := h26c.2.1
                              have p26_2 := h26c.2.2.1
                              have p26_3 := h26c.2.2.2
                              linarith only [h0, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p26_1, u3ehi2]
                            · have p26_0 := h26c.1
                              have p26_1 := h26c.2.1
                              have p26_2 := h26c.2.2.1
                              have p26_3 := h26c.2.2.2
                              linarith only [h0, h24, hc01, hc45, hlam, hphi, ht0b, ht5b, p26_1]
                            · have p26_0 := h26c.1
                              have p26_1 := h26c.2.1
                              have p26_2 := h26c.2.2.1
                              have p26_3 := h26c.2.2.2
                              linarith only [h0, h22, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p26_1, u3ehi2]
                            · have p26_0 := h26c.1
                              have p26_1 := h26c.2.1
                              have p26_2 := h26c.2.2.1
                              have p26_3 := h26c.2.2.2
                              linarith only [h0, hlam, p26_1]
                            · have p26_0 := h26c.1
                              have p26_1 := h26c.2.1
                              have p26_2 := h26c.2.2.1
                              have p26_3 := h26c.2.2.2
                              linarith only [hlam, p26_0]
                            · have p26_0 := h26c.1
                              have p26_1 := h26c.2.1
                              have p26_2 := h26c.2.2.1
                              have p26_3 := h26c.2.2.2
                              linarith only [hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p26_1, u3ehi2]
                            · have p26_0 := h26c.1
                              have p26_1 := h26c.2.1
                              have p26_2 := h26c.2.2.1
                              have p26_3 := h26c.2.2.2
                              linarith only [h0, h20, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p26_1, u3ehi2]
                            · have p26_0 := h26c.1
                              have p26_1 := h26c.2.1
                              have p26_2 := h26c.2.2.1
                              have p26_3 := h26c.2.2.2
                              linarith only [h0, hc01, hc25, hlam, hphi, ht0b, ht5b, p26_1]
                            · have p26_0 := h26c.1
                              have p26_1 := h26c.2.1
                              have p26_2 := h26c.2.2.1
                              have p26_3 := h26c.2.2.2
                              linarith only [h1, hlam, p26_0]
                            · have p26_0 := h26c.1
                              have p26_1 := h26c.2.1
                              have p26_2 := h26c.2.2.1
                              have p26_3 := h26c.2.2.2
                              linarith only [h4, hlam, p26_0]
                            · have p26_0 := h26c.1
                              have p26_1 := h26c.2.1
                              have p26_2 := h26c.2.2.1
                              have p26_3 := h26c.2.2.2
                              linarith only [hlam, p26_0]
                            · have p26_0 := h26c.1
                              have p26_1 := h26c.2.1
                              have p26_2 := h26c.2.2.1
                              have p26_3 := h26c.2.2.2
                              linarith only [h20, hlam, p26_1]
                            · have p26_0 := h26c.1
                              have p26_1 := h26c.2.1
                              have p26_2 := h26c.2.2.1
                              have p26_3 := h26c.2.2.2
                              linarith only [h22, hlam, p26_1]
                            · have p26_0 := h26c.1
                              have p26_1 := h26c.2.1
                              have p26_2 := h26c.2.2.1
                              have p26_3 := h26c.2.2.2
                              linarith only [h2, hlam, p26_0]
                            · have p26_0 := h26c.1
                              have p26_1 := h26c.2.1
                              have p26_2 := h26c.2.2.1
                              have p26_3 := h26c.2.2.2
                              linarith only [h5, hlam, p26_0]
                            · have p26_0 := h26c.1
                              have p26_1 := h26c.2.1
                              have p26_2 := h26c.2.2.1
                              have p26_3 := h26c.2.2.2
                              linarith only [hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p26_1, u3ehi2]
                            · have p26_0 := h26c.1
                              have p26_1 := h26c.2.1
                              have p26_2 := h26c.2.2.1
                              have p26_3 := h26c.2.2.2
                              linarith only [hlam, p26_0]
                            · have p26_0 := h26c.1
                              have p26_1 := h26c.2.1
                              have p26_2 := h26c.2.2.1
                              have p26_3 := h26c.2.2.2
                              linarith only [h0, h22, h5, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p26_1, u3ehi2]
                            · have p26_0 := h26c.1
                              have p26_1 := h26c.2.1
                              have p26_2 := h26c.2.2.1
                              have p26_3 := h26c.2.2.2
                              linarith only [h3, hlam, p26_0]
                            · have p26_0 := h26c.1
                              have p26_1 := h26c.2.1
                              have p26_2 := h26c.2.2.1
                              have p26_3 := h26c.2.2.2
                              linarith only [h6, hlam, p26_0]
                            · have p26_0 := h26c.1
                              have p26_1 := h26c.2.1
                              have p26_2 := h26c.2.2.1
                              have p26_3 := h26c.2.2.2
                              linarith only [hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p26_1, u3ehi2]
                            · have p26_0 := h26c.1
                              have p26_1 := h26c.2.1
                              have p26_2 := h26c.2.2.1
                              have p26_3 := h26c.2.2.2
                              linarith only [h24, hlam, p26_1]
                            · have p26_0 := h26c.1
                              have p26_1 := h26c.2.1
                              have p26_2 := h26c.2.2.1
                              have p26_3 := h26c.2.2.2
                              linarith only [hlam, p26_0]
                          · linarith only [h25, h4, h7, hc45, hlam, hphi, ht34, u3ehi2]
                        · linarith only [h0, h19, h20, h24, h5, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h54 | h54
                    · linarith only [h4, h54, h7, hlam]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h56 | h56
                      · linarith only [h17, h4, h56, hlam]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h58 | h58
                        · linarith only [h0, h19, h5, h58, hc01, hc14, hlam, hphi, ht0b, ht45, ht5b]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h60 | h60
                          · linarith only [h19, h4, h60, h7, hc34, hlam, hphi, u3ehi2]
                          · linarith only [h4, h60, h7, hc45, hlam, hphi, ht34, u3ehi2]
            · linarith only [h0, h3, h4, h6, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
          · linarith only [h0, h2, h4, h5, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h65 | h65
          · rcases m.htr 1 2 5 (by decide) (by decide) with h66 | h66
            · rcases m.htr 1 3 4 (by decide) (by decide) with h67 | h67
              · rcases m.htr 1 3 5 (by decide) (by decide) with h68 | h68
                · rcases m.htr 1 4 5 (by decide) (by decide) with h69 | h69
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h70 | h70
                    · linarith only [h0, h1, h4, h65, h70, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                    · linarith only [h4, h65, h67, h70, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h73 | h73
                    · linarith only [h0, h1, h4, h65, h73, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                    · linarith only [h4, h67, h69, h73, hc12, hc45, hlam, hphi, ht23, ht34]
                · linarith only [h67, h68, hc35, hlam, hphi, u3ehi3]
              · linarith only [h4, h65, h67, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h78 | h78
              · rcases m.htr 1 3 5 (by decide) (by decide) with h79 | h79
                · rcases m.htr 1 4 5 (by decide) (by decide) with h80 | h80
                  · linarith only [h65, h66, h80, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h82 | h82
                    · linarith only [h0, h1, h4, h65, h82, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                    · linarith only [h4, h65, h78, h82, hc13, hc24, hlam, hphi, ht01, ht0b, ht45, ht5b]
                · linarith only [h78, h79, hc35, hlam, hphi, u3ehi3]
              · linarith only [h4, h65, h78, hlam]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h87 | h87
            · rcases m.htr 1 3 4 (by decide) (by decide) with h88 | h88
              · rcases m.htr 1 3 5 (by decide) (by decide) with h89 | h89
                · rcases m.htr 1 4 5 (by decide) (by decide) with h90 | h90
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h91 | h91
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h92 | h92
                      · linarith only [h0, h1, h65, h87, h91, h92, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi4]
                      · linarith only [h4, h88, h92, hc35, hlam, hphi, u3ehi3]
                    · linarith only [h4, h88, h91, hlam]
                  · linarith only [h65, h87, h90, hlam]
                · linarith only [h88, h89, hc35, hlam, hphi, u3ehi3]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h98 | h98
                · linarith only [h88, h98, hc34, hlam, hphi, u3ehi4]
                · linarith only [h4, h87, h98, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h101 | h101
              · rcases m.htr 1 3 5 (by decide) (by decide) with h102 | h102
                · rcases m.htr 1 4 5 (by decide) (by decide) with h103 | h103
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h104 | h104
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h105 | h105
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h106 | h106
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h107 | h107
                          · rcases h2bigk with h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c | h108c
                            · have p108_0 := h108c.1
                              have p108_1 := h108c.2.1
                              have p108_2 := h108c.2.2.1
                              have p108_3 := h108c.2.2.2
                              linarith only [hlam, p108_0]
                            · have p108_0 := h108c.1
                              have p108_1 := h108c.2.1
                              have p108_2 := h108c.2.2.1
                              have p108_3 := h108c.2.2.2
                              rcases p108_3 (m.d 0 2) (by simp) with h110 | h110
                              · rcases p108_3 (m.d 1 2) (by simp) with h111 | h111
                                · linarith only [h0, h111, hlam]
                                · rcases p108_3 (m.d 2 3) (by simp) with h113 | h113
                                  · linarith only [h1, h113, hlam]
                                  · linarith only [h113, h4, hlam]
                              · linarith only [h0, h110, hlam]
                            · have p108_0 := h108c.1
                              have p108_1 := h108c.2.1
                              have p108_2 := h108c.2.2.1
                              have p108_3 := h108c.2.2.2
                              linarith only [h0, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p108_1, u3ehi2]
                            · have p108_0 := h108c.1
                              have p108_1 := h108c.2.1
                              have p108_2 := h108c.2.2.1
                              have p108_3 := h108c.2.2.2
                              linarith only [h0, h65, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p108_1]
                            · have p108_0 := h108c.1
                              have p108_1 := h108c.2.1
                              have p108_2 := h108c.2.2.1
                              have p108_3 := h108c.2.2.2
                              linarith only [h0, h87, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p108_1]
                            · have p108_0 := h108c.1
                              have p108_1 := h108c.2.1
                              have p108_2 := h108c.2.2.1
                              have p108_3 := h108c.2.2.2
                              linarith only [h0, hlam, p108_1]
                            · have p108_0 := h108c.1
                              have p108_1 := h108c.2.1
                              have p108_2 := h108c.2.2.1
                              have p108_3 := h108c.2.2.2
                              linarith only [hlam, p108_0]
                            · have p108_0 := h108c.1
                              have p108_1 := h108c.2.1
                              have p108_2 := h108c.2.2.1
                              have p108_3 := h108c.2.2.2
                              linarith only [h4, hlam, p108_0]
                            · have p108_0 := h108c.1
                              have p108_1 := h108c.2.1
                              have p108_2 := h108c.2.2.1
                              have p108_3 := h108c.2.2.2
                              linarith only [h65, hlam, p108_0]
                            · have p108_0 := h108c.1
                              have p108_1 := h108c.2.1
                              have p108_2 := h108c.2.2.1
                              have p108_3 := h108c.2.2.2
                              linarith only [h87, hlam, p108_0]
                            · have p108_0 := h108c.1
                              have p108_1 := h108c.2.1
                              have p108_2 := h108c.2.2.1
                              have p108_3 := h108c.2.2.2
                              linarith only [h1, hlam, p108_0]
                            · have p108_0 := h108c.1
                              have p108_1 := h108c.2.1
                              have p108_2 := h108c.2.2.1
                              have p108_3 := h108c.2.2.2
                              linarith only [hc12, hc23, hlam, hphi, p108_1]
                            · have p108_0 := h108c.1
                              have p108_1 := h108c.2.1
                              have p108_2 := h108c.2.2.1
                              have p108_3 := h108c.2.2.2
                              linarith only [hlam, p108_0]
                            · have p108_0 := h108c.1
                              have p108_1 := h108c.2.1
                              have p108_2 := h108c.2.2.1
                              have p108_3 := h108c.2.2.2
                              linarith only [h0, h1, h101, h107, h65, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p108_1, u3ehi4]
                            · have p108_0 := h108c.1
                              have p108_1 := h108c.2.1
                              have p108_2 := h108c.2.2.1
                              have p108_3 := h108c.2.2.2
                              linarith only [h0, h1, h102, h87, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p108_1, u3ehi4]
                            · have p108_0 := h108c.1
                              have p108_1 := h108c.2.1
                              have p108_2 := h108c.2.2.1
                              have p108_3 := h108c.2.2.2
                              linarith only [h2, hlam, p108_0]
                            · have p108_0 := h108c.1
                              have p108_1 := h108c.2.1
                              have p108_2 := h108c.2.2.1
                              have p108_3 := h108c.2.2.2
                              linarith only [hc12, hc24, hlam, hphi, p108_1]
                            · have p108_0 := h108c.1
                              have p108_1 := h108c.2.1
                              have p108_2 := h108c.2.2.1
                              have p108_3 := h108c.2.2.2
                              linarith only [h104, hlam, p108_0]
                            · have p108_0 := h108c.1
                              have p108_1 := h108c.2.1
                              have p108_2 := h108c.2.2.1
                              have p108_3 := h108c.2.2.2
                              linarith only [hlam, p108_0]
                            · have p108_0 := h108c.1
                              have p108_1 := h108c.2.1
                              have p108_2 := h108c.2.2.1
                              have p108_3 := h108c.2.2.2
                              linarith only [h0, h1, h102, h104, h87, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p108_1, u3ehi4]
                            · have p108_0 := h108c.1
                              have p108_1 := h108c.2.1
                              have p108_2 := h108c.2.2.1
                              have p108_3 := h108c.2.2.2
                              linarith only [h3, hlam, p108_0]
                            · have p108_0 := h108c.1
                              have p108_1 := h108c.2.1
                              have p108_2 := h108c.2.2.1
                              have p108_3 := h108c.2.2.2
                              linarith only [hc12, hc25, hlam, hphi, p108_1]
                            · have p108_0 := h108c.1
                              have p108_1 := h108c.2.1
                              have p108_2 := h108c.2.2.1
                              have p108_3 := h108c.2.2.2
                              linarith only [h105, hlam, p108_0]
                            · have p108_0 := h108c.1
                              have p108_1 := h108c.2.1
                              have p108_2 := h108c.2.2.1
                              have p108_3 := h108c.2.2.2
                              linarith only [h106, hlam, p108_1]
                            · have p108_0 := h108c.1
                              have p108_1 := h108c.2.1
                              have p108_2 := h108c.2.2.1
                              have p108_3 := h108c.2.2.2
                              linarith only [hlam, p108_0]
                          · linarith only [h0, h1, h103, h104, h107, h65, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                        · linarith only [h103, h106, h65, hlam]
                      · linarith only [h101, h105, h4, hc35, hlam, hphi, u3ehi3]
                    · linarith only [h101, h104, h4, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h144 | h144
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h145 | h145
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h146 | h146
                        · linarith only [h0, h101, h103, h146, h2, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h148 | h148
                          · linarith only [h0, h1, h101, h146, h148, h4, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
                          · rcases h2bigk with h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c | h150c
                            · have p150_0 := h150c.1
                              have p150_1 := h150c.2.1
                              have p150_2 := h150c.2.2.1
                              have p150_3 := h150c.2.2.2
                              linarith only [hlam, p150_0]
                            · have p150_0 := h150c.1
                              have p150_1 := h150c.2.1
                              have p150_2 := h150c.2.2.1
                              have p150_3 := h150c.2.2.2
                              rcases p150_3 (m.d 0 2) (by simp) with h152 | h152
                              · rcases p150_3 (m.d 1 2) (by simp) with h153 | h153
                                · linarith only [h0, h153, hlam]
                                · rcases p150_3 (m.d 2 3) (by simp) with h155 | h155
                                  · linarith only [h1, h155, hlam]
                                  · linarith only [h155, h4, hlam]
                              · linarith only [h0, h152, hlam]
                            · have p150_0 := h150c.1
                              have p150_1 := h150c.2.1
                              have p150_2 := h150c.2.2.1
                              have p150_3 := h150c.2.2.2
                              linarith only [h0, h102, h148, h4, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p150_1, u3ehi3]
                            · have p150_0 := h150c.1
                              have p150_1 := h150c.2.1
                              have p150_2 := h150c.2.2.1
                              have p150_3 := h150c.2.2.2
                              linarith only [h0, h101, h65, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p150_1, u3ehi3]
                            · have p150_0 := h150c.1
                              have p150_1 := h150c.2.1
                              have p150_2 := h150c.2.2.1
                              have p150_3 := h150c.2.2.2
                              linarith only [h0, h87, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p150_1]
                            · have p150_0 := h150c.1
                              have p150_1 := h150c.2.1
                              have p150_2 := h150c.2.2.1
                              have p150_3 := h150c.2.2.2
                              linarith only [h0, hlam, p150_1]
                            · have p150_0 := h150c.1
                              have p150_1 := h150c.2.1
                              have p150_2 := h150c.2.2.1
                              have p150_3 := h150c.2.2.2
                              linarith only [hlam, p150_0]
                            · have p150_0 := h150c.1
                              have p150_1 := h150c.2.1
                              have p150_2 := h150c.2.2.1
                              have p150_3 := h150c.2.2.2
                              linarith only [h4, hlam, p150_0]
                            · have p150_0 := h150c.1
                              have p150_1 := h150c.2.1
                              have p150_2 := h150c.2.2.1
                              have p150_3 := h150c.2.2.2
                              linarith only [h65, hlam, p150_0]
                            · have p150_0 := h150c.1
                              have p150_1 := h150c.2.1
                              have p150_2 := h150c.2.2.1
                              have p150_3 := h150c.2.2.2
                              linarith only [h87, hlam, p150_0]
                            · have p150_0 := h150c.1
                              have p150_1 := h150c.2.1
                              have p150_2 := h150c.2.2.1
                              have p150_3 := h150c.2.2.2
                              linarith only [h1, hlam, p150_0]
                            · have p150_0 := h150c.1
                              have p150_1 := h150c.2.1
                              have p150_2 := h150c.2.2.1
                              have p150_3 := h150c.2.2.2
                              linarith only [hc12, hc23, hlam, hphi, p150_1]
                            · have p150_0 := h150c.1
                              have p150_1 := h150c.2.1
                              have p150_2 := h150c.2.2.1
                              have p150_3 := h150c.2.2.2
                              linarith only [hlam, p150_0]
                            · have p150_0 := h150c.1
                              have p150_1 := h150c.2.1
                              have p150_2 := h150c.2.2.1
                              have p150_3 := h150c.2.2.2
                              linarith only [h0, h1, h101, h65, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p150_1, u3ehi3]
                            · have p150_0 := h150c.1
                              have p150_1 := h150c.2.1
                              have p150_2 := h150c.2.2.1
                              have p150_3 := h150c.2.2.2
                              linarith only [h0, h1, h101, h103, h87, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p150_1, u3ehi3]
                            · have p150_0 := h150c.1
                              have p150_1 := h150c.2.1
                              have p150_2 := h150c.2.2.1
                              have p150_3 := h150c.2.2.2
                              linarith only [h2, hlam, p150_0]
                            · have p150_0 := h150c.1
                              have p150_1 := h150c.2.1
                              have p150_2 := h150c.2.2.1
                              have p150_3 := h150c.2.2.2
                              linarith only [hc12, hc24, hlam, hphi, p150_1]
                            · have p150_0 := h150c.1
                              have p150_1 := h150c.2.1
                              have p150_2 := h150c.2.2.1
                              have p150_3 := h150c.2.2.2
                              linarith only [h144, hlam, p150_0]
                            · have p150_0 := h150c.1
                              have p150_1 := h150c.2.1
                              have p150_2 := h150c.2.2.1
                              have p150_3 := h150c.2.2.2
                              linarith only [hlam, p150_0]
                            · have p150_0 := h150c.1
                              have p150_1 := h150c.2.1
                              have p150_2 := h150c.2.2.1
                              have p150_3 := h150c.2.2.2
                              linarith only [h146, hlam, p150_0]
                            · have p150_0 := h150c.1
                              have p150_1 := h150c.2.1
                              have p150_2 := h150c.2.2.1
                              have p150_3 := h150c.2.2.2
                              linarith only [h3, hlam, p150_0]
                            · have p150_0 := h150c.1
                              have p150_1 := h150c.2.1
                              have p150_2 := h150c.2.2.1
                              have p150_3 := h150c.2.2.2
                              linarith only [hc12, hc25, hlam, hphi, p150_1]
                            · have p150_0 := h150c.1
                              have p150_1 := h150c.2.1
                              have p150_2 := h150c.2.2.1
                              have p150_3 := h150c.2.2.2
                              linarith only [h145, hlam, p150_0]
                            · have p150_0 := h150c.1
                              have p150_1 := h150c.2.1
                              have p150_2 := h150c.2.2.1
                              have p150_3 := h150c.2.2.2
                              linarith only [h0, h1, h145, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b, p150_1]
                            · have p150_0 := h150c.1
                              have p150_1 := h150c.2.1
                              have p150_2 := h150c.2.2.1
                              have p150_3 := h150c.2.2.2
                              linarith only [hlam, p150_0]
                      · linarith only [h102, h145, h4, hlam]
                    · linarith only [h102, h144, h4, hc34, hlam, hphi, u3ehi4]
                · linarith only [h101, h102, hc35, hlam, hphi, u3ehi3]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h185 | h185
                · linarith only [h101, h185, hc34, hlam, hphi, u3ehi4]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h187 | h187
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h188 | h188
                    · linarith only [h0, h1, h101, h188, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h190 | h190
                      · linarith only [h185, h188, h190, hc34, hlam, hphi, u3ehi1]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h192 | h192
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h193 | h193
                          · rcases h2bigk with h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c | h194c
                            · have p194_0 := h194c.1
                              have p194_1 := h194c.2.1
                              have p194_2 := h194c.2.2.1
                              have p194_3 := h194c.2.2.2
                              linarith only [hlam, p194_0]
                            · have p194_0 := h194c.1
                              have p194_1 := h194c.2.1
                              have p194_2 := h194c.2.2.1
                              have p194_3 := h194c.2.2.2
                              rcases p194_3 (m.d 0 2) (by simp) with h196 | h196
                              · rcases p194_3 (m.d 1 2) (by simp) with h197 | h197
                                · linarith only [h0, h197, hlam]
                                · rcases p194_3 (m.d 2 3) (by simp) with h199 | h199
                                  · linarith only [h1, h199, hlam]
                                  · linarith only [h199, h4, hlam]
                              · linarith only [h0, h196, hlam]
                            · have p194_0 := h194c.1
                              have p194_1 := h194c.2.1
                              have p194_2 := h194c.2.2.1
                              have p194_3 := h194c.2.2.2
                              linarith only [h0, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p194_1, u3ehi2]
                            · have p194_0 := h194c.1
                              have p194_1 := h194c.2.1
                              have p194_2 := h194c.2.2.1
                              have p194_3 := h194c.2.2.2
                              linarith only [h0, h65, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p194_1]
                            · have p194_0 := h194c.1
                              have p194_1 := h194c.2.1
                              have p194_2 := h194c.2.2.1
                              have p194_3 := h194c.2.2.2
                              linarith only [h0, h87, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p194_1]
                            · have p194_0 := h194c.1
                              have p194_1 := h194c.2.1
                              have p194_2 := h194c.2.2.1
                              have p194_3 := h194c.2.2.2
                              linarith only [h0, hlam, p194_1]
                            · have p194_0 := h194c.1
                              have p194_1 := h194c.2.1
                              have p194_2 := h194c.2.2.1
                              have p194_3 := h194c.2.2.2
                              linarith only [hlam, p194_0]
                            · have p194_0 := h194c.1
                              have p194_1 := h194c.2.1
                              have p194_2 := h194c.2.2.1
                              have p194_3 := h194c.2.2.2
                              linarith only [h4, hlam, p194_0]
                            · have p194_0 := h194c.1
                              have p194_1 := h194c.2.1
                              have p194_2 := h194c.2.2.1
                              have p194_3 := h194c.2.2.2
                              linarith only [h65, hlam, p194_0]
                            · have p194_0 := h194c.1
                              have p194_1 := h194c.2.1
                              have p194_2 := h194c.2.2.1
                              have p194_3 := h194c.2.2.2
                              linarith only [h87, hlam, p194_0]
                            · have p194_0 := h194c.1
                              have p194_1 := h194c.2.1
                              have p194_2 := h194c.2.2.1
                              have p194_3 := h194c.2.2.2
                              linarith only [h1, hlam, p194_0]
                            · have p194_0 := h194c.1
                              have p194_1 := h194c.2.1
                              have p194_2 := h194c.2.2.1
                              have p194_3 := h194c.2.2.2
                              linarith only [hc12, hc23, hlam, hphi, p194_1]
                            · have p194_0 := h194c.1
                              have p194_1 := h194c.2.1
                              have p194_2 := h194c.2.2.1
                              have p194_3 := h194c.2.2.2
                              linarith only [hlam, p194_0]
                            · have p194_0 := h194c.1
                              have p194_1 := h194c.2.1
                              have p194_2 := h194c.2.2.1
                              have p194_3 := h194c.2.2.2
                              linarith only [h188, hlam, p194_1]
                            · have p194_0 := h194c.1
                              have p194_1 := h194c.2.1
                              have p194_2 := h194c.2.2.1
                              have p194_3 := h194c.2.2.2
                              linarith only [h190, hlam, p194_1]
                            · have p194_0 := h194c.1
                              have p194_1 := h194c.2.1
                              have p194_2 := h194c.2.2.1
                              have p194_3 := h194c.2.2.2
                              linarith only [h2, hlam, p194_0]
                            · have p194_0 := h194c.1
                              have p194_1 := h194c.2.1
                              have p194_2 := h194c.2.2.1
                              have p194_3 := h194c.2.2.2
                              linarith only [hc12, hc24, hlam, hphi, p194_1]
                            · have p194_0 := h194c.1
                              have p194_1 := h194c.2.1
                              have p194_2 := h194c.2.2.1
                              have p194_3 := h194c.2.2.2
                              linarith only [h0, h2, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p194_1, u3ehi2]
                            · have p194_0 := h194c.1
                              have p194_1 := h194c.2.1
                              have p194_2 := h194c.2.2.1
                              have p194_3 := h194c.2.2.2
                              linarith only [hlam, p194_0]
                            · have p194_0 := h194c.1
                              have p194_1 := h194c.2.1
                              have p194_2 := h194c.2.2.1
                              have p194_3 := h194c.2.2.2
                              linarith only [h0, h185, h2, h87, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, p194_1, u3ehi1]
                            · have p194_0 := h194c.1
                              have p194_1 := h194c.2.1
                              have p194_2 := h194c.2.2.1
                              have p194_3 := h194c.2.2.2
                              linarith only [h3, hlam, p194_0]
                            · have p194_0 := h194c.1
                              have p194_1 := h194c.2.1
                              have p194_2 := h194c.2.2.1
                              have p194_3 := h194c.2.2.2
                              linarith only [hc12, hc25, hlam, hphi, p194_1]
                            · have p194_0 := h194c.1
                              have p194_1 := h194c.2.1
                              have p194_2 := h194c.2.2.1
                              have p194_3 := h194c.2.2.2
                              linarith only [h0, h3, h4, hc01, hc12, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p194_1]
                            · have p194_0 := h194c.1
                              have p194_1 := h194c.2.1
                              have p194_2 := h194c.2.2.1
                              have p194_3 := h194c.2.2.2
                              linarith only [h192, hlam, p194_1]
                            · have p194_0 := h194c.1
                              have p194_1 := h194c.2.1
                              have p194_2 := h194c.2.2.1
                              have p194_3 := h194c.2.2.2
                              linarith only [hlam, p194_0]
                          · linarith only [h0, h187, h193, h2, h65, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi3]
                        · linarith only [h187, h192, h65, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h228 | h228
                    · linarith only [h0, h1, h101, h228, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h230 | h230
                      · linarith only [h228, h230, hc34, hlam, hphi, u3ehi4]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h232 | h232
                        · linarith only [h0, h101, h187, h2, h232, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h234 | h234
                          · linarith only [h228, h232, h234, hc34, hlam, hphi, u3ehi2]
                          · linarith only [h101, h234, hc45, hlam, hphi, ht34, u3ehi1]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h237 | h237
        · rcases m.htr 1 2 4 (by decide) (by decide) with h238 | h238
          · rcases m.htr 1 2 5 (by decide) (by decide) with h239 | h239
            · linarith only [h0, h1, h239, h3, hc01, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi0]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h241 | h241
              · rcases m.htr 1 3 5 (by decide) (by decide) with h242 | h242
                · linarith only [h237, h239, h242, hlam]
                · linarith only [h241, h242, hc35, hlam, hphi, u3ehi3]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h245 | h245
                · linarith only [h241, h245, hc34, hlam, hphi, u3ehi4]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h247 | h247
                  · linarith only [h238, h239, h247, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h249 | h249
                    · linarith only [h1, h249, h3, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h251 | h251
                      · linarith only [h0, h238, h245, h249, h251, h3, hc25, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                      · linarith only [h1, h251, h3, hc35, hlam, hphi, u3ehi2]
          · linarith only [h2, h237, h238, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi2]
        · linarith only [h1, h237, h3, hc12, hc25, hlam, hphi]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h256 | h256
      · rcases m.htr 1 2 3 (by decide) (by decide) with h257 | h257
        · rcases m.htr 1 2 4 (by decide) (by decide) with h258 | h258
          · linarith only [h0, h2, h258, hlam]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h260 | h260
            · rcases m.htr 1 3 4 (by decide) (by decide) with h261 | h261
              · linarith only [h257, h258, h261, hlam]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h263 | h263
                · linarith only [h261, h263, hc34, hlam, hphi, u3ehi4]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h265 | h265
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h266 | h266
                    · linarith only [h0, h257, h261, h266, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, u3ehi1]
                    · linarith only [h1, h2, h266, hc34, hlam, hphi, u3ehi2]
                  · linarith only [h257, h258, h265, hc45, hlam, hphi, ht34, u3ehi2]
            · linarith only [h2, h256, h257, h260, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi2]
        · linarith only [h1, h2, h257, hc12, hc24, hlam, hphi]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h272 | h272
        · rcases m.htr 1 2 4 (by decide) (by decide) with h273 | h273
          · linarith only [h0, h2, h273, hlam]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h275 | h275
            · linarith only [h0, h256, h275, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h277 | h277
              · linarith only [h272, h273, h277, hlam]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h279 | h279
                · linarith only [h277, h279, hc34, hlam, hphi, u3ehi4]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h281 | h281
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h282 | h282
                    · linarith only [h0, h2, h272, h277, h282, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                    · linarith only [h1, h2, h282, hc34, hlam, hphi, u3ehi2]
                  · linarith only [h272, h273, h281, hc45, hlam, hphi, ht34, u3ehi2]
        · linarith only [h1, h2, h272, hc12, hc24, hlam, hphi]
  · rcases m.htr 0 2 4 (by decide) (by decide) with h287 | h287
    · rcases m.htr 0 2 5 (by decide) (by decide) with h288 | h288
      · rcases m.htr 1 2 3 (by decide) (by decide) with h289 | h289
        · linarith only [h0, h1, h287, h289, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h291 | h291
          · rcases m.htr 1 2 5 (by decide) (by decide) with h292 | h292
            · rcases m.htr 1 3 4 (by decide) (by decide) with h293 | h293
              · rcases m.htr 1 3 5 (by decide) (by decide) with h294 | h294
                · rcases m.htr 1 4 5 (by decide) (by decide) with h295 | h295
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h296 | h296
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h297 | h297
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h298 | h298
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h299 | h299
                          · rcases h2bigk with h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c | h300c
                            · have p300_0 := h300c.1
                              have p300_1 := h300c.2.1
                              have p300_2 := h300c.2.2.1
                              have p300_3 := h300c.2.2.2
                              linarith only [hlam, p300_0]
                            · have p300_0 := h300c.1
                              have p300_1 := h300c.2.1
                              have p300_2 := h300c.2.2.1
                              have p300_3 := h300c.2.2.2
                              linarith only [h291, h297, h298, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p300_1, u3ehi4]
                            · have p300_0 := h300c.1
                              have p300_1 := h300c.2.1
                              have p300_2 := h300c.2.2.1
                              have p300_3 := h300c.2.2.2
                              linarith only [h1, hlam, p300_0]
                            · have p300_0 := h300c.1
                              have p300_1 := h300c.2.1
                              have p300_2 := h300c.2.2.1
                              have p300_3 := h300c.2.2.2
                              linarith only [h1, h297, h298, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p300_1, u3ehi4]
                            · have p300_0 := h300c.1
                              have p300_1 := h300c.2.1
                              have p300_2 := h300c.2.2.1
                              have p300_3 := h300c.2.2.2
                              linarith only [h1, h297, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p300_1, u3ehi4]
                            · have p300_0 := h300c.1
                              have p300_1 := h300c.2.1
                              have p300_2 := h300c.2.2.1
                              have p300_3 := h300c.2.2.2
                              linarith only [h0, hlam, p300_1]
                            · have p300_0 := h300c.1
                              have p300_1 := h300c.2.1
                              have p300_2 := h300c.2.2.1
                              have p300_3 := h300c.2.2.2
                              linarith only [hlam, p300_0]
                            · have p300_0 := h300c.1
                              have p300_1 := h300c.2.1
                              have p300_2 := h300c.2.2.1
                              have p300_3 := h300c.2.2.2
                              linarith only [h289, hlam, p300_0]
                            · have p300_0 := h300c.1
                              have p300_1 := h300c.2.1
                              have p300_2 := h300c.2.2.1
                              have p300_3 := h300c.2.2.2
                              linarith only [h297, h298, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p300_1, u3ehi4]
                            · have p300_0 := h300c.1
                              have p300_1 := h300c.2.1
                              have p300_2 := h300c.2.2.1
                              have p300_3 := h300c.2.2.2
                              linarith only [h0, h1, h297, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p300_1, u3ehi4]
                            · have p300_0 := h300c.1
                              have p300_1 := h300c.2.1
                              have p300_2 := h300c.2.2.1
                              have p300_3 := h300c.2.2.2
                              linarith only [hc02, hc23, hlam, hphi, p300_1]
                            · have p300_0 := h300c.1
                              have p300_1 := h300c.2.1
                              have p300_2 := h300c.2.2.1
                              have p300_3 := h300c.2.2.2
                              linarith only [hc12, hc23, hlam, hphi, p300_1]
                            · have p300_0 := h300c.1
                              have p300_1 := h300c.2.1
                              have p300_2 := h300c.2.2.1
                              have p300_3 := h300c.2.2.2
                              linarith only [hlam, p300_0]
                            · have p300_0 := h300c.1
                              have p300_1 := h300c.2.1
                              have p300_2 := h300c.2.2.1
                              have p300_3 := h300c.2.2.2
                              linarith only [h297, h298, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p300_1, u3ehi4]
                            · have p300_0 := h300c.1
                              have p300_1 := h300c.2.1
                              have p300_2 := h300c.2.2.1
                              have p300_3 := h300c.2.2.2
                              linarith only [h297, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p300_1, u3ehi4]
                            · have p300_0 := h300c.1
                              have p300_1 := h300c.2.1
                              have p300_2 := h300c.2.2.1
                              have p300_3 := h300c.2.2.2
                              linarith only [h287, hlam, p300_0]
                            · have p300_0 := h300c.1
                              have p300_1 := h300c.2.1
                              have p300_2 := h300c.2.2.1
                              have p300_3 := h300c.2.2.2
                              linarith only [h291, hlam, p300_0]
                            · have p300_0 := h300c.1
                              have p300_1 := h300c.2.1
                              have p300_2 := h300c.2.2.1
                              have p300_3 := h300c.2.2.2
                              linarith only [h296, hlam, p300_0]
                            · have p300_0 := h300c.1
                              have p300_1 := h300c.2.1
                              have p300_2 := h300c.2.2.1
                              have p300_3 := h300c.2.2.2
                              linarith only [hlam, p300_0]
                            · have p300_0 := h300c.1
                              have p300_1 := h300c.2.1
                              have p300_2 := h300c.2.2.1
                              have p300_3 := h300c.2.2.2
                              linarith only [h0, h291, h297, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p300_1, u3ehi4]
                            · have p300_0 := h300c.1
                              have p300_1 := h300c.2.1
                              have p300_2 := h300c.2.2.1
                              have p300_3 := h300c.2.2.2
                              linarith only [h288, hlam, p300_0]
                            · have p300_0 := h300c.1
                              have p300_1 := h300c.2.1
                              have p300_2 := h300c.2.2.1
                              have p300_3 := h300c.2.2.2
                              linarith only [h292, hlam, p300_0]
                            · have p300_0 := h300c.1
                              have p300_1 := h300c.2.1
                              have p300_2 := h300c.2.2.1
                              have p300_3 := h300c.2.2.2
                              linarith only [h297, hlam, p300_0]
                            · have p300_0 := h300c.1
                              have p300_1 := h300c.2.1
                              have p300_2 := h300c.2.2.1
                              have p300_3 := h300c.2.2.2
                              linarith only [h298, hlam, p300_1]
                            · have p300_0 := h300c.1
                              have p300_1 := h300c.2.1
                              have p300_2 := h300c.2.2.1
                              have p300_3 := h300c.2.2.2
                              linarith only [hlam, p300_0]
                          · linarith only [h0, h1, h291, h295, h299, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                        · linarith only [h0, h1, h291, h295, h296, h298, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                      · linarith only [h1, h287, h296, h297, hc35, hlam, hphi, u3ehi3]
                    · linarith only [h0, h1, h291, h293, h296, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h330 | h330
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h331 | h331
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h332 | h332
                        · linarith only [h0, h1, h291, h295, h332, hc14, hc23, hlam, hphi, ht01, ht0b, ht12, ht45, ht5b]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h334 | h334
                          · linarith only [h291, h295, h330, h334, hlam]
                          · rcases h2bigk with h336c | h336c | h336c | h336c | h336c | h336c | h336c | h336c | h336c | h336c | h336c | h336c | h336c | h336c | h336c | h336c | h336c | h336c | h336c | h336c | h336c | h336c | h336c | h336c | h336c
                            · have p336_0 := h336c.1
                              have p336_1 := h336c.2.1
                              have p336_2 := h336c.2.2.1
                              have p336_3 := h336c.2.2.2
                              linarith only [hlam, p336_0]
                            · have p336_0 := h336c.1
                              have p336_1 := h336c.2.1
                              have p336_2 := h336c.2.2.1
                              have p336_3 := h336c.2.2.2
                              linarith only [h1, h292, h330, h332, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p336_1, u3ehi3]
                            · have p336_0 := h336c.1
                              have p336_1 := h336c.2.1
                              have p336_2 := h336c.2.2.1
                              have p336_3 := h336c.2.2.2
                              linarith only [h1, hlam, p336_0]
                            · have p336_0 := h336c.1
                              have p336_1 := h336c.2.1
                              have p336_2 := h336c.2.2.1
                              have p336_3 := h336c.2.2.2
                              linarith only [h1, h330, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p336_1, u3ehi3]
                            · have p336_0 := h336c.1
                              have p336_1 := h336c.2.1
                              have p336_2 := h336c.2.2.1
                              have p336_3 := h336c.2.2.2
                              linarith only [h1, h330, h332, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p336_1, u3ehi3]
                            · have p336_0 := h336c.1
                              have p336_1 := h336c.2.1
                              have p336_2 := h336c.2.2.1
                              have p336_3 := h336c.2.2.2
                              linarith only [h0, hlam, p336_1]
                            · have p336_0 := h336c.1
                              have p336_1 := h336c.2.1
                              have p336_2 := h336c.2.2.1
                              have p336_3 := h336c.2.2.2
                              linarith only [hlam, p336_0]
                            · have p336_0 := h336c.1
                              have p336_1 := h336c.2.1
                              have p336_2 := h336c.2.2.1
                              have p336_3 := h336c.2.2.2
                              linarith only [h289, hlam, p336_0]
                            · have p336_0 := h336c.1
                              have p336_1 := h336c.2.1
                              have p336_2 := h336c.2.2.1
                              have p336_3 := h336c.2.2.2
                              linarith only [h330, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p336_1, u3ehi3]
                            · have p336_0 := h336c.1
                              have p336_1 := h336c.2.1
                              have p336_2 := h336c.2.2.1
                              have p336_3 := h336c.2.2.2
                              linarith only [h0, h1, h330, h332, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p336_1, u3ehi3]
                            · have p336_0 := h336c.1
                              have p336_1 := h336c.2.1
                              have p336_2 := h336c.2.2.1
                              have p336_3 := h336c.2.2.2
                              linarith only [hc02, hc23, hlam, hphi, p336_1]
                            · have p336_0 := h336c.1
                              have p336_1 := h336c.2.1
                              have p336_2 := h336c.2.2.1
                              have p336_3 := h336c.2.2.2
                              linarith only [hc12, hc23, hlam, hphi, p336_1]
                            · have p336_0 := h336c.1
                              have p336_1 := h336c.2.1
                              have p336_2 := h336c.2.2.1
                              have p336_3 := h336c.2.2.2
                              linarith only [hlam, p336_0]
                            · have p336_0 := h336c.1
                              have p336_1 := h336c.2.1
                              have p336_2 := h336c.2.2.1
                              have p336_3 := h336c.2.2.2
                              linarith only [h330, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p336_1, u3ehi3]
                            · have p336_0 := h336c.1
                              have p336_1 := h336c.2.1
                              have p336_2 := h336c.2.2.1
                              have p336_3 := h336c.2.2.2
                              linarith only [h330, h332, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p336_1, u3ehi3]
                            · have p336_0 := h336c.1
                              have p336_1 := h336c.2.1
                              have p336_2 := h336c.2.2.1
                              have p336_3 := h336c.2.2.2
                              linarith only [h287, hlam, p336_0]
                            · have p336_0 := h336c.1
                              have p336_1 := h336c.2.1
                              have p336_2 := h336c.2.2.1
                              have p336_3 := h336c.2.2.2
                              linarith only [h291, hlam, p336_0]
                            · have p336_0 := h336c.1
                              have p336_1 := h336c.2.1
                              have p336_2 := h336c.2.2.1
                              have p336_3 := h336c.2.2.2
                              linarith only [h330, hlam, p336_0]
                            · have p336_0 := h336c.1
                              have p336_1 := h336c.2.1
                              have p336_2 := h336c.2.2.1
                              have p336_3 := h336c.2.2.2
                              linarith only [hlam, p336_0]
                            · have p336_0 := h336c.1
                              have p336_1 := h336c.2.1
                              have p336_2 := h336c.2.2.1
                              have p336_3 := h336c.2.2.2
                              linarith only [h332, hlam, p336_0]
                            · have p336_0 := h336c.1
                              have p336_1 := h336c.2.1
                              have p336_2 := h336c.2.2.1
                              have p336_3 := h336c.2.2.2
                              linarith only [h288, hlam, p336_0]
                            · have p336_0 := h336c.1
                              have p336_1 := h336c.2.1
                              have p336_2 := h336c.2.2.1
                              have p336_3 := h336c.2.2.2
                              linarith only [h292, hlam, p336_0]
                            · have p336_0 := h336c.1
                              have p336_1 := h336c.2.1
                              have p336_2 := h336c.2.2.1
                              have p336_3 := h336c.2.2.2
                              linarith only [h331, hlam, p336_0]
                            · have p336_0 := h336c.1
                              have p336_1 := h336c.2.1
                              have p336_2 := h336c.2.2.1
                              have p336_3 := h336c.2.2.2
                              linarith only [h0, h292, h330, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p336_1, u3ehi3]
                            · have p336_0 := h336c.1
                              have p336_1 := h336c.2.1
                              have p336_2 := h336c.2.2.1
                              have p336_3 := h336c.2.2.2
                              linarith only [hlam, p336_0]
                      · linarith only [h1, h287, h330, h331, hc35, hlam, hphi, u3ehi3]
                    · linarith only [h0, h1, h292, h293, h295, h330, hlam]
                · linarith only [h293, h294, hc35, hlam, hphi, u3ehi3]
              · linarith only [h289, h291, h293, hlam]
            · linarith only [h1, h288, h292, hc12, hc23, hlam, hphi]
          · linarith only [h1, h287, h291, hc12, hc23, hlam, hphi]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h368 | h368
        · linarith only [h0, h1, h287, h368, hc01, hc24, hlam, hphi, ht0b, ht45, ht5b]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h370 | h370
          · rcases m.htr 1 2 5 (by decide) (by decide) with h371 | h371
            · linarith only [h0, h288, h371, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h373 | h373
              · rcases m.htr 1 3 5 (by decide) (by decide) with h374 | h374
                · rcases m.htr 1 4 5 (by decide) (by decide) with h375 | h375
                  · linarith only [h370, h371, h375, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h377 | h377
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h378 | h378
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h379 | h379
                        · linarith only [h370, h371, h375, h379, hlam]
                        · linarith only [h0, h288, h370, h377, h379, hc45, hlam, hphi, ht34, u3ehi3]
                      · linarith only [h0, h1, h370, h374, h377, h378, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, u3ehi3]
                    · linarith only [h368, h373, h377, hlam]
                · linarith only [h373, h374, hc35, hlam, hphi, u3ehi3]
              · linarith only [h368, h370, h373, hlam]
          · linarith only [h1, h287, h370, hc12, hc23, hlam, hphi]
    · rcases m.htr 0 2 5 (by decide) (by decide) with h387 | h387
      · rcases m.htr 1 2 3 (by decide) (by decide) with h388 | h388
        · linarith only [h0, h1, h387, h388, hc01, hc25, hlam, hphi, ht0b, ht5b]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h390 | h390
          · linarith only [h0, h287, h390, hlam]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h392 | h392
            · rcases m.htr 1 3 4 (by decide) (by decide) with h393 | h393
              · rcases m.htr 1 3 5 (by decide) (by decide) with h394 | h394
                · rcases m.htr 1 4 5 (by decide) (by decide) with h395 | h395
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h396 | h396
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h397 | h397
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h398 | h398
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h399 | h399
                          · rcases h2bigk with h400c | h400c | h400c | h400c | h400c | h400c | h400c | h400c | h400c | h400c | h400c | h400c | h400c | h400c | h400c | h400c | h400c | h400c | h400c | h400c | h400c | h400c | h400c | h400c | h400c
                            · have p400_0 := h400c.1
                              have p400_1 := h400c.2.1
                              have p400_2 := h400c.2.2.1
                              have p400_3 := h400c.2.2.2
                              linarith only [hlam, p400_0]
                            · have p400_0 := h400c.1
                              have p400_1 := h400c.2.1
                              have p400_2 := h400c.2.2.1
                              have p400_3 := h400c.2.2.2
                              linarith only [h392, h397, hc02, hlam, hphi, ht0b, ht34, ht45, ht5b, p400_1, u3ehi4]
                            · have p400_0 := h400c.1
                              have p400_1 := h400c.2.1
                              have p400_2 := h400c.2.2.1
                              have p400_3 := h400c.2.2.2
                              linarith only [h1, hlam, p400_0]
                            · have p400_0 := h400c.1
                              have p400_1 := h400c.2.1
                              have p400_2 := h400c.2.2.1
                              have p400_3 := h400c.2.2.2
                              linarith only [h287, hlam, p400_0]
                            · have p400_0 := h400c.1
                              have p400_1 := h400c.2.1
                              have p400_2 := h400c.2.2.1
                              have p400_3 := h400c.2.2.2
                              linarith only [h287, h396, h397, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p400_1, u3ehi4]
                            · have p400_0 := h400c.1
                              have p400_1 := h400c.2.1
                              have p400_2 := h400c.2.2.1
                              have p400_3 := h400c.2.2.2
                              linarith only [h0, hlam, p400_1]
                            · have p400_0 := h400c.1
                              have p400_1 := h400c.2.1
                              have p400_2 := h400c.2.2.1
                              have p400_3 := h400c.2.2.2
                              linarith only [hlam, p400_0]
                            · have p400_0 := h400c.1
                              have p400_1 := h400c.2.1
                              have p400_2 := h400c.2.2.1
                              have p400_3 := h400c.2.2.2
                              linarith only [h388, hlam, p400_0]
                            · have p400_0 := h400c.1
                              have p400_1 := h400c.2.1
                              have p400_2 := h400c.2.2.1
                              have p400_3 := h400c.2.2.2
                              linarith only [h390, hlam, p400_0]
                            · have p400_0 := h400c.1
                              have p400_1 := h400c.2.1
                              have p400_2 := h400c.2.2.1
                              have p400_3 := h400c.2.2.2
                              linarith only [h397, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p400_1, u3ehi4]
                            · have p400_0 := h400c.1
                              have p400_1 := h400c.2.1
                              have p400_2 := h400c.2.2.1
                              have p400_3 := h400c.2.2.2
                              linarith only [hc02, hc23, hlam, hphi, p400_1]
                            · have p400_0 := h400c.1
                              have p400_1 := h400c.2.1
                              have p400_2 := h400c.2.2.1
                              have p400_3 := h400c.2.2.2
                              linarith only [hc12, hc23, hlam, hphi, p400_1]
                            · have p400_0 := h400c.1
                              have p400_1 := h400c.2.1
                              have p400_2 := h400c.2.2.1
                              have p400_3 := h400c.2.2.2
                              linarith only [hlam, p400_0]
                            · have p400_0 := h400c.1
                              have p400_1 := h400c.2.1
                              have p400_2 := h400c.2.2.1
                              have p400_3 := h400c.2.2.2
                              linarith only [h287, h387, h397, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p400_1, u3ehi4]
                            · have p400_0 := h400c.1
                              have p400_1 := h400c.2.1
                              have p400_2 := h400c.2.2.1
                              have p400_3 := h400c.2.2.2
                              linarith only [h397, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p400_1, u3ehi4]
                            · have p400_0 := h400c.1
                              have p400_1 := h400c.2.1
                              have p400_2 := h400c.2.2.1
                              have p400_3 := h400c.2.2.2
                              linarith only [h0, h392, h397, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p400_1, u3ehi4]
                            · have p400_0 := h400c.1
                              have p400_1 := h400c.2.1
                              have p400_2 := h400c.2.2.1
                              have p400_3 := h400c.2.2.2
                              linarith only [h392, h397, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p400_1, u3ehi4]
                            · have p400_0 := h400c.1
                              have p400_1 := h400c.2.1
                              have p400_2 := h400c.2.2.1
                              have p400_3 := h400c.2.2.2
                              linarith only [h396, hlam, p400_0]
                            · have p400_0 := h400c.1
                              have p400_1 := h400c.2.1
                              have p400_2 := h400c.2.2.1
                              have p400_3 := h400c.2.2.2
                              linarith only [hlam, p400_0]
                            · have p400_0 := h400c.1
                              have p400_1 := h400c.2.1
                              have p400_2 := h400c.2.2.1
                              have p400_3 := h400c.2.2.2
                              linarith only [h396, h397, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p400_1, u3ehi4]
                            · have p400_0 := h400c.1
                              have p400_1 := h400c.2.1
                              have p400_2 := h400c.2.2.1
                              have p400_3 := h400c.2.2.2
                              linarith only [h387, hlam, p400_0]
                            · have p400_0 := h400c.1
                              have p400_1 := h400c.2.1
                              have p400_2 := h400c.2.2.1
                              have p400_3 := h400c.2.2.2
                              linarith only [h392, hlam, p400_0]
                            · have p400_0 := h400c.1
                              have p400_1 := h400c.2.1
                              have p400_2 := h400c.2.2.1
                              have p400_3 := h400c.2.2.2
                              linarith only [h397, hlam, p400_0]
                            · have p400_0 := h400c.1
                              have p400_1 := h400c.2.1
                              have p400_2 := h400c.2.2.1
                              have p400_3 := h400c.2.2.2
                              linarith only [h398, hlam, p400_1]
                            · have p400_0 := h400c.1
                              have p400_1 := h400c.2.1
                              have p400_2 := h400c.2.2.1
                              have p400_3 := h400c.2.2.2
                              linarith only [hlam, p400_0]
                          · linarith only [h1, h387, h398, h399, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi3]
                        · linarith only [h0, h287, h392, h395, h398, hlam]
                      · linarith only [h388, h393, h397, hc35, hlam, hphi, u3ehi3]
                    · linarith only [h388, h393, h396, hlam]
                  · linarith only [h390, h392, h395, hlam]
                · linarith only [h393, h394, hc35, hlam, hphi, u3ehi3]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h432 | h432
                · linarith only [h393, h432, hc34, hlam, hphi, u3ehi4]
                · linarith only [h388, h392, h432, hlam]
            · linarith only [h287, h387, h392, hc12, hc24, hlam, hphi]
      · rcases m.htr 1 2 3 (by decide) (by decide) with h436 | h436
        · linarith only [h0, h1, h436, hlam]
        · rcases m.htr 1 2 4 (by decide) (by decide) with h438 | h438
          · linarith only [h0, h287, h438, hlam]
          · rcases m.htr 1 2 5 (by decide) (by decide) with h440 | h440
            · linarith only [h0, h387, h440, hlam]
            · rcases m.htr 1 3 4 (by decide) (by decide) with h442 | h442
              · rcases m.htr 1 3 5 (by decide) (by decide) with h443 | h443
                · rcases m.htr 1 4 5 (by decide) (by decide) with h444 | h444
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h445 | h445
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h446 | h446
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h447 | h447
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h448 | h448
                          · rcases h2bigk with h449c | h449c | h449c | h449c | h449c | h449c | h449c | h449c | h449c | h449c | h449c | h449c | h449c | h449c | h449c | h449c | h449c | h449c | h449c | h449c | h449c | h449c | h449c | h449c | h449c
                            · have p449_0 := h449c.1
                              have p449_1 := h449c.2.1
                              have p449_2 := h449c.2.2.1
                              have p449_3 := h449c.2.2.2
                              linarith only [hlam, p449_0]
                            · have p449_0 := h449c.1
                              have p449_1 := h449c.2.1
                              have p449_2 := h449c.2.2.1
                              have p449_3 := h449c.2.2.2
                              linarith only [h387, h445, h447, hc12, hc23, hlam, hphi, p449_1]
                            · have p449_0 := h449c.1
                              have p449_1 := h449c.2.1
                              have p449_2 := h449c.2.2.1
                              have p449_3 := h449c.2.2.2
                              linarith only [h1, hlam, p449_0]
                            · have p449_0 := h449c.1
                              have p449_1 := h449c.2.1
                              have p449_2 := h449c.2.2.1
                              have p449_3 := h449c.2.2.2
                              linarith only [h287, hlam, p449_0]
                            · have p449_0 := h449c.1
                              have p449_1 := h449c.2.1
                              have p449_2 := h449c.2.2.1
                              have p449_3 := h449c.2.2.2
                              linarith only [h387, hlam, p449_0]
                            · have p449_0 := h449c.1
                              have p449_1 := h449c.2.1
                              have p449_2 := h449c.2.2.1
                              have p449_3 := h449c.2.2.2
                              linarith only [h0, hlam, p449_1]
                            · have p449_0 := h449c.1
                              have p449_1 := h449c.2.1
                              have p449_2 := h449c.2.2.1
                              have p449_3 := h449c.2.2.2
                              linarith only [hlam, p449_0]
                            · have p449_0 := h449c.1
                              have p449_1 := h449c.2.1
                              have p449_2 := h449c.2.2.1
                              have p449_3 := h449c.2.2.2
                              linarith only [h436, hlam, p449_0]
                            · have p449_0 := h449c.1
                              have p449_1 := h449c.2.1
                              have p449_2 := h449c.2.2.1
                              have p449_3 := h449c.2.2.2
                              linarith only [h438, hlam, p449_0]
                            · have p449_0 := h449c.1
                              have p449_1 := h449c.2.1
                              have p449_2 := h449c.2.2.1
                              have p449_3 := h449c.2.2.2
                              linarith only [h440, hlam, p449_0]
                            · have p449_0 := h449c.1
                              have p449_1 := h449c.2.1
                              have p449_2 := h449c.2.2.1
                              have p449_3 := h449c.2.2.2
                              linarith only [hc02, hc23, hlam, hphi, p449_1]
                            · have p449_0 := h449c.1
                              have p449_1 := h449c.2.1
                              have p449_2 := h449c.2.2.1
                              have p449_3 := h449c.2.2.2
                              linarith only [hc12, hc23, hlam, hphi, p449_1]
                            · have p449_0 := h449c.1
                              have p449_1 := h449c.2.1
                              have p449_2 := h449c.2.2.1
                              have p449_3 := h449c.2.2.2
                              linarith only [hlam, p449_0]
                            · have p449_0 := h449c.1
                              have p449_1 := h449c.2.1
                              have p449_2 := h449c.2.2.1
                              have p449_3 := h449c.2.2.2
                              linarith only [h0, h287, hc12, hc23, hlam, hphi, p449_1]
                            · have p449_0 := h449c.1
                              have p449_1 := h449c.2.1
                              have p449_2 := h449c.2.2.1
                              have p449_3 := h449c.2.2.2
                              linarith only [h0, h387, hc12, hc23, hlam, hphi, p449_1]
                            · have p449_0 := h449c.1
                              have p449_1 := h449c.2.1
                              have p449_2 := h449c.2.2.1
                              have p449_3 := h449c.2.2.2
                              linarith only [h0, hc12, hc24, hlam, hphi, p449_1]
                            · have p449_0 := h449c.1
                              have p449_1 := h449c.2.1
                              have p449_2 := h449c.2.2.1
                              have p449_3 := h449c.2.2.2
                              linarith only [hc12, hc24, hlam, hphi, p449_1]
                            · have p449_0 := h449c.1
                              have p449_1 := h449c.2.1
                              have p449_2 := h449c.2.2.1
                              have p449_3 := h449c.2.2.2
                              linarith only [h445, hlam, p449_0]
                            · have p449_0 := h449c.1
                              have p449_1 := h449c.2.1
                              have p449_2 := h449c.2.2.1
                              have p449_3 := h449c.2.2.2
                              linarith only [hlam, p449_0]
                            · have p449_0 := h449c.1
                              have p449_1 := h449c.2.1
                              have p449_2 := h449c.2.2.1
                              have p449_3 := h449c.2.2.2
                              linarith only [h0, h387, h445, hc12, hc23, hlam, hphi, p449_1]
                            · have p449_0 := h449c.1
                              have p449_1 := h449c.2.1
                              have p449_2 := h449c.2.2.1
                              have p449_3 := h449c.2.2.2
                              linarith only [h0, hc12, hc25, hlam, hphi, p449_1]
                            · have p449_0 := h449c.1
                              have p449_1 := h449c.2.1
                              have p449_2 := h449c.2.2.1
                              have p449_3 := h449c.2.2.2
                              linarith only [hc12, hc25, hlam, hphi, p449_1]
                            · have p449_0 := h449c.1
                              have p449_1 := h449c.2.1
                              have p449_2 := h449c.2.2.1
                              have p449_3 := h449c.2.2.2
                              linarith only [h446, hlam, p449_0]
                            · have p449_0 := h449c.1
                              have p449_1 := h449c.2.1
                              have p449_2 := h449c.2.2.1
                              have p449_3 := h449c.2.2.2
                              linarith only [h447, hlam, p449_1]
                            · have p449_0 := h449c.1
                              have p449_1 := h449c.2.1
                              have p449_2 := h449c.2.2.1
                              have p449_3 := h449c.2.2.2
                              linarith only [hlam, p449_0]
                          · rcases h2bigk with h475c | h475c | h475c | h475c | h475c | h475c | h475c | h475c | h475c | h475c | h475c | h475c | h475c | h475c | h475c | h475c | h475c | h475c | h475c | h475c | h475c | h475c | h475c | h475c | h475c
                            · have p475_0 := h475c.1
                              have p475_1 := h475c.2.1
                              have p475_2 := h475c.2.2.1
                              have p475_3 := h475c.2.2.2
                              linarith only [hlam, p475_0]
                            · have p475_0 := h475c.1
                              have p475_1 := h475c.2.1
                              have p475_2 := h475c.2.2.1
                              have p475_3 := h475c.2.2.2
                              linarith only [h1, hc12, hc23, hlam, hphi, p475_1]
                            · have p475_0 := h475c.1
                              have p475_1 := h475c.2.1
                              have p475_2 := h475c.2.2.1
                              have p475_3 := h475c.2.2.2
                              linarith only [h1, hlam, p475_0]
                            · have p475_0 := h475c.1
                              have p475_1 := h475c.2.1
                              have p475_2 := h475c.2.2.1
                              have p475_3 := h475c.2.2.2
                              linarith only [h287, hlam, p475_0]
                            · have p475_0 := h475c.1
                              have p475_1 := h475c.2.1
                              have p475_2 := h475c.2.2.1
                              have p475_3 := h475c.2.2.2
                              linarith only [h387, hlam, p475_0]
                            · have p475_0 := h475c.1
                              have p475_1 := h475c.2.1
                              have p475_2 := h475c.2.2.1
                              have p475_3 := h475c.2.2.2
                              linarith only [h0, hlam, p475_1]
                            · have p475_0 := h475c.1
                              have p475_1 := h475c.2.1
                              have p475_2 := h475c.2.2.1
                              have p475_3 := h475c.2.2.2
                              linarith only [hlam, p475_0]
                            · have p475_0 := h475c.1
                              have p475_1 := h475c.2.1
                              have p475_2 := h475c.2.2.1
                              have p475_3 := h475c.2.2.2
                              linarith only [h436, hlam, p475_0]
                            · have p475_0 := h475c.1
                              have p475_1 := h475c.2.1
                              have p475_2 := h475c.2.2.1
                              have p475_3 := h475c.2.2.2
                              linarith only [h438, hlam, p475_0]
                            · have p475_0 := h475c.1
                              have p475_1 := h475c.2.1
                              have p475_2 := h475c.2.2.1
                              have p475_3 := h475c.2.2.2
                              linarith only [h440, hlam, p475_0]
                            · have p475_0 := h475c.1
                              have p475_1 := h475c.2.1
                              have p475_2 := h475c.2.2.1
                              have p475_3 := h475c.2.2.2
                              linarith only [hc02, hc23, hlam, hphi, p475_1]
                            · have p475_0 := h475c.1
                              have p475_1 := h475c.2.1
                              have p475_2 := h475c.2.2.1
                              have p475_3 := h475c.2.2.2
                              linarith only [hc12, hc23, hlam, hphi, p475_1]
                            · have p475_0 := h475c.1
                              have p475_1 := h475c.2.1
                              have p475_2 := h475c.2.2.1
                              have p475_3 := h475c.2.2.2
                              linarith only [hlam, p475_0]
                            · have p475_0 := h475c.1
                              have p475_1 := h475c.2.1
                              have p475_2 := h475c.2.2.1
                              have p475_3 := h475c.2.2.2
                              linarith only [h438, h444, h448, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p475_1, u3ehi3]
                            · have p475_0 := h475c.1
                              have p475_1 := h475c.2.1
                              have p475_2 := h475c.2.2.1
                              have p475_3 := h475c.2.2.2
                              linarith only [h0, h387, hc12, hc23, hlam, hphi, p475_1]
                            · have p475_0 := h475c.1
                              have p475_1 := h475c.2.1
                              have p475_2 := h475c.2.2.1
                              have p475_3 := h475c.2.2.2
                              linarith only [h0, hc12, hc24, hlam, hphi, p475_1]
                            · have p475_0 := h475c.1
                              have p475_1 := h475c.2.1
                              have p475_2 := h475c.2.2.1
                              have p475_3 := h475c.2.2.2
                              linarith only [hc12, hc24, hlam, hphi, p475_1]
                            · have p475_0 := h475c.1
                              have p475_1 := h475c.2.1
                              have p475_2 := h475c.2.2.1
                              have p475_3 := h475c.2.2.2
                              linarith only [h445, hlam, p475_0]
                            · have p475_0 := h475c.1
                              have p475_1 := h475c.2.1
                              have p475_2 := h475c.2.2.1
                              have p475_3 := h475c.2.2.2
                              linarith only [hlam, p475_0]
                            · have p475_0 := h475c.1
                              have p475_1 := h475c.2.1
                              have p475_2 := h475c.2.2.1
                              have p475_3 := h475c.2.2.2
                              linarith only [h440, h444, h445, h448, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p475_1, u3ehi3]
                            · have p475_0 := h475c.1
                              have p475_1 := h475c.2.1
                              have p475_2 := h475c.2.2.1
                              have p475_3 := h475c.2.2.2
                              linarith only [h0, hc12, hc25, hlam, hphi, p475_1]
                            · have p475_0 := h475c.1
                              have p475_1 := h475c.2.1
                              have p475_2 := h475c.2.2.1
                              have p475_3 := h475c.2.2.2
                              linarith only [hc12, hc25, hlam, hphi, p475_1]
                            · have p475_0 := h475c.1
                              have p475_1 := h475c.2.1
                              have p475_2 := h475c.2.2.1
                              have p475_3 := h475c.2.2.2
                              linarith only [h446, hlam, p475_0]
                            · have p475_0 := h475c.1
                              have p475_1 := h475c.2.1
                              have p475_2 := h475c.2.2.1
                              have p475_3 := h475c.2.2.2
                              linarith only [h447, hlam, p475_1]
                            · have p475_0 := h475c.1
                              have p475_1 := h475c.2.1
                              have p475_2 := h475c.2.2.1
                              have p475_3 := h475c.2.2.2
                              linarith only [hlam, p475_0]
                        · linarith only [h0, h287, h436, h442, h444, h447, hc12, hc23, hlam, hphi]
                      · linarith only [h436, h442, h446, hc35, hlam, hphi, u3ehi3]
                    · linarith only [h436, h442, h445, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h504 | h504
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h505 | h505
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h506 | h506
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h507 | h507
                          · linarith only [h442, h444, h507, hlam]
                          · rcases h2bigk with h509c | h509c | h509c | h509c | h509c | h509c | h509c | h509c | h509c | h509c | h509c | h509c | h509c | h509c | h509c | h509c | h509c | h509c | h509c | h509c | h509c | h509c | h509c | h509c | h509c
                            · have p509_0 := h509c.1
                              have p509_1 := h509c.2.1
                              have p509_2 := h509c.2.2.1
                              have p509_3 := h509c.2.2.2
                              linarith only [hlam, p509_0]
                            · have p509_0 := h509c.1
                              have p509_1 := h509c.2.1
                              have p509_2 := h509c.2.2.1
                              have p509_3 := h509c.2.2.2
                              linarith only [h1, hc12, hc23, hlam, hphi, p509_1]
                            · have p509_0 := h509c.1
                              have p509_1 := h509c.2.1
                              have p509_2 := h509c.2.2.1
                              have p509_3 := h509c.2.2.2
                              linarith only [h1, hlam, p509_0]
                            · have p509_0 := h509c.1
                              have p509_1 := h509c.2.1
                              have p509_2 := h509c.2.2.1
                              have p509_3 := h509c.2.2.2
                              linarith only [h287, hlam, p509_0]
                            · have p509_0 := h509c.1
                              have p509_1 := h509c.2.1
                              have p509_2 := h509c.2.2.1
                              have p509_3 := h509c.2.2.2
                              linarith only [h387, hlam, p509_0]
                            · have p509_0 := h509c.1
                              have p509_1 := h509c.2.1
                              have p509_2 := h509c.2.2.1
                              have p509_3 := h509c.2.2.2
                              linarith only [h0, hlam, p509_1]
                            · have p509_0 := h509c.1
                              have p509_1 := h509c.2.1
                              have p509_2 := h509c.2.2.1
                              have p509_3 := h509c.2.2.2
                              linarith only [hlam, p509_0]
                            · have p509_0 := h509c.1
                              have p509_1 := h509c.2.1
                              have p509_2 := h509c.2.2.1
                              have p509_3 := h509c.2.2.2
                              linarith only [h436, hlam, p509_0]
                            · have p509_0 := h509c.1
                              have p509_1 := h509c.2.1
                              have p509_2 := h509c.2.2.1
                              have p509_3 := h509c.2.2.2
                              linarith only [h438, hlam, p509_0]
                            · have p509_0 := h509c.1
                              have p509_1 := h509c.2.1
                              have p509_2 := h509c.2.2.1
                              have p509_3 := h509c.2.2.2
                              linarith only [h440, hlam, p509_0]
                            · have p509_0 := h509c.1
                              have p509_1 := h509c.2.1
                              have p509_2 := h509c.2.2.1
                              have p509_3 := h509c.2.2.2
                              linarith only [hc02, hc23, hlam, hphi, p509_1]
                            · have p509_0 := h509c.1
                              have p509_1 := h509c.2.1
                              have p509_2 := h509c.2.2.1
                              have p509_3 := h509c.2.2.2
                              linarith only [hc12, hc23, hlam, hphi, p509_1]
                            · have p509_0 := h509c.1
                              have p509_1 := h509c.2.1
                              have p509_2 := h509c.2.2.1
                              have p509_3 := h509c.2.2.2
                              linarith only [hlam, p509_0]
                            · have p509_0 := h509c.1
                              have p509_1 := h509c.2.1
                              have p509_2 := h509c.2.2.1
                              have p509_3 := h509c.2.2.2
                              linarith only [h442, h444, h506, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p509_1, u3ehi3]
                            · have p509_0 := h509c.1
                              have p509_1 := h509c.2.1
                              have p509_2 := h509c.2.2.1
                              have p509_3 := h509c.2.2.2
                              linarith only [h0, h387, hc12, hc23, hlam, hphi, p509_1]
                            · have p509_0 := h509c.1
                              have p509_1 := h509c.2.1
                              have p509_2 := h509c.2.2.1
                              have p509_3 := h509c.2.2.2
                              linarith only [h0, hc12, hc24, hlam, hphi, p509_1]
                            · have p509_0 := h509c.1
                              have p509_1 := h509c.2.1
                              have p509_2 := h509c.2.2.1
                              have p509_3 := h509c.2.2.2
                              linarith only [hc12, hc24, hlam, hphi, p509_1]
                            · have p509_0 := h509c.1
                              have p509_1 := h509c.2.1
                              have p509_2 := h509c.2.2.1
                              have p509_3 := h509c.2.2.2
                              linarith only [h504, hlam, p509_0]
                            · have p509_0 := h509c.1
                              have p509_1 := h509c.2.1
                              have p509_2 := h509c.2.2.1
                              have p509_3 := h509c.2.2.2
                              linarith only [hlam, p509_0]
                            · have p509_0 := h509c.1
                              have p509_1 := h509c.2.1
                              have p509_2 := h509c.2.2.1
                              have p509_3 := h509c.2.2.2
                              linarith only [h0, h387, h504, hc12, hc23, hlam, hphi, p509_1]
                            · have p509_0 := h509c.1
                              have p509_1 := h509c.2.1
                              have p509_2 := h509c.2.2.1
                              have p509_3 := h509c.2.2.2
                              linarith only [h0, hc12, hc25, hlam, hphi, p509_1]
                            · have p509_0 := h509c.1
                              have p509_1 := h509c.2.1
                              have p509_2 := h509c.2.2.1
                              have p509_3 := h509c.2.2.2
                              linarith only [hc12, hc25, hlam, hphi, p509_1]
                            · have p509_0 := h509c.1
                              have p509_1 := h509c.2.1
                              have p509_2 := h509c.2.2.1
                              have p509_3 := h509c.2.2.2
                              linarith only [h505, hlam, p509_0]
                            · have p509_0 := h509c.1
                              have p509_1 := h509c.2.1
                              have p509_2 := h509c.2.2.1
                              have p509_3 := h509c.2.2.2
                              linarith only [h506, hlam, p509_1]
                            · have p509_0 := h509c.1
                              have p509_1 := h509c.2.1
                              have p509_2 := h509c.2.2.1
                              have p509_3 := h509c.2.2.2
                              linarith only [hlam, p509_0]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h535 | h535
                          · linarith only [h0, h287, h506, h535, hc12, hc34, hlam, hphi, ht23]
                          · rcases h2bigk with h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c | h537c
                            · have p537_0 := h537c.1
                              have p537_1 := h537c.2.1
                              have p537_2 := h537c.2.2.1
                              have p537_3 := h537c.2.2.2
                              linarith only [hlam, p537_0]
                            · have p537_0 := h537c.1
                              have p537_1 := h537c.2.1
                              have p537_2 := h537c.2.2.1
                              have p537_3 := h537c.2.2.2
                              linarith only [h287, hc12, hc24, hlam, hphi, p537_1]
                            · have p537_0 := h537c.1
                              have p537_1 := h537c.2.1
                              have p537_2 := h537c.2.2.1
                              have p537_3 := h537c.2.2.2
                              linarith only [h1, hlam, p537_0]
                            · have p537_0 := h537c.1
                              have p537_1 := h537c.2.1
                              have p537_2 := h537c.2.2.1
                              have p537_3 := h537c.2.2.2
                              linarith only [h287, hlam, p537_0]
                            · have p537_0 := h537c.1
                              have p537_1 := h537c.2.1
                              have p537_2 := h537c.2.2.1
                              have p537_3 := h537c.2.2.2
                              linarith only [h387, hlam, p537_0]
                            · have p537_0 := h537c.1
                              have p537_1 := h537c.2.1
                              have p537_2 := h537c.2.2.1
                              have p537_3 := h537c.2.2.2
                              linarith only [h0, hlam, p537_1]
                            · have p537_0 := h537c.1
                              have p537_1 := h537c.2.1
                              have p537_2 := h537c.2.2.1
                              have p537_3 := h537c.2.2.2
                              linarith only [hlam, p537_0]
                            · have p537_0 := h537c.1
                              have p537_1 := h537c.2.1
                              have p537_2 := h537c.2.2.1
                              have p537_3 := h537c.2.2.2
                              linarith only [h436, hlam, p537_0]
                            · have p537_0 := h537c.1
                              have p537_1 := h537c.2.1
                              have p537_2 := h537c.2.2.1
                              have p537_3 := h537c.2.2.2
                              linarith only [h438, hlam, p537_0]
                            · have p537_0 := h537c.1
                              have p537_1 := h537c.2.1
                              have p537_2 := h537c.2.2.1
                              have p537_3 := h537c.2.2.2
                              linarith only [h440, hlam, p537_0]
                            · have p537_0 := h537c.1
                              have p537_1 := h537c.2.1
                              have p537_2 := h537c.2.2.1
                              have p537_3 := h537c.2.2.2
                              linarith only [hc02, hc23, hlam, hphi, p537_1]
                            · have p537_0 := h537c.1
                              have p537_1 := h537c.2.1
                              have p537_2 := h537c.2.2.1
                              have p537_3 := h537c.2.2.2
                              linarith only [hc12, hc23, hlam, hphi, p537_1]
                            · have p537_0 := h537c.1
                              have p537_1 := h537c.2.1
                              have p537_2 := h537c.2.2.1
                              have p537_3 := h537c.2.2.2
                              linarith only [hlam, p537_0]
                            · have p537_0 := h537c.1
                              have p537_1 := h537c.2.1
                              have p537_2 := h537c.2.2.1
                              have p537_3 := h537c.2.2.2
                              linarith only [h438, h442, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p537_1, u3ehi3]
                            · have p537_0 := h537c.1
                              have p537_1 := h537c.2.1
                              have p537_2 := h537c.2.2.1
                              have p537_3 := h537c.2.2.2
                              linarith only [h0, h387, hc12, hc23, hlam, hphi, p537_1]
                            · have p537_0 := h537c.1
                              have p537_1 := h537c.2.1
                              have p537_2 := h537c.2.2.1
                              have p537_3 := h537c.2.2.2
                              linarith only [h0, hc12, hc24, hlam, hphi, p537_1]
                            · have p537_0 := h537c.1
                              have p537_1 := h537c.2.1
                              have p537_2 := h537c.2.2.1
                              have p537_3 := h537c.2.2.2
                              linarith only [hc12, hc24, hlam, hphi, p537_1]
                            · have p537_0 := h537c.1
                              have p537_1 := h537c.2.1
                              have p537_2 := h537c.2.2.1
                              have p537_3 := h537c.2.2.2
                              linarith only [h504, hlam, p537_0]
                            · have p537_0 := h537c.1
                              have p537_1 := h537c.2.1
                              have p537_2 := h537c.2.2.1
                              have p537_3 := h537c.2.2.2
                              linarith only [hlam, p537_0]
                            · have p537_0 := h537c.1
                              have p537_1 := h537c.2.1
                              have p537_2 := h537c.2.2.1
                              have p537_3 := h537c.2.2.2
                              linarith only [h506, hlam, p537_0]
                            · have p537_0 := h537c.1
                              have p537_1 := h537c.2.1
                              have p537_2 := h537c.2.2.1
                              have p537_3 := h537c.2.2.2
                              linarith only [h0, hc12, hc25, hlam, hphi, p537_1]
                            · have p537_0 := h537c.1
                              have p537_1 := h537c.2.1
                              have p537_2 := h537c.2.2.1
                              have p537_3 := h537c.2.2.2
                              linarith only [hc12, hc25, hlam, hphi, p537_1]
                            · have p537_0 := h537c.1
                              have p537_1 := h537c.2.1
                              have p537_2 := h537c.2.2.1
                              have p537_3 := h537c.2.2.2
                              linarith only [h505, hlam, p537_0]
                            · have p537_0 := h537c.1
                              have p537_1 := h537c.2.1
                              have p537_2 := h537c.2.2.1
                              have p537_3 := h537c.2.2.2
                              linarith only [h506, hc24, hc45, hlam, hphi, p537_1]
                            · have p537_0 := h537c.1
                              have p537_1 := h537c.2.1
                              have p537_2 := h537c.2.2.1
                              have p537_3 := h537c.2.2.2
                              linarith only [hlam, p537_0]
                      · linarith only [h436, h442, h505, hc35, hlam, hphi, u3ehi3]
                    · linarith only [h436, h442, h504, hlam]
                · linarith only [h442, h443, hc35, hlam, hphi, u3ehi3]
              · rcases m.htr 1 3 5 (by decide) (by decide) with h566 | h566
                · linarith only [h442, h566, hc34, hlam, hphi, u3ehi4]
                · rcases m.htr 1 4 5 (by decide) (by decide) with h568 | h568
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h569 | h569
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h570 | h570
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h571 | h571
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h572 | h572
                          · rcases h2bigk with h573c | h573c | h573c | h573c | h573c | h573c | h573c | h573c | h573c | h573c | h573c | h573c | h573c | h573c | h573c | h573c | h573c | h573c | h573c | h573c | h573c | h573c | h573c | h573c | h573c
                            · have p573_0 := h573c.1
                              have p573_1 := h573c.2.1
                              have p573_2 := h573c.2.2.1
                              have p573_3 := h573c.2.2.2
                              linarith only [hlam, p573_0]
                            · have p573_0 := h573c.1
                              have p573_1 := h573c.2.1
                              have p573_2 := h573c.2.2.1
                              have p573_3 := h573c.2.2.2
                              linarith only [h1, hc12, hc23, hlam, hphi, p573_1]
                            · have p573_0 := h573c.1
                              have p573_1 := h573c.2.1
                              have p573_2 := h573c.2.2.1
                              have p573_3 := h573c.2.2.2
                              linarith only [h1, hlam, p573_0]
                            · have p573_0 := h573c.1
                              have p573_1 := h573c.2.1
                              have p573_2 := h573c.2.2.1
                              have p573_3 := h573c.2.2.2
                              linarith only [h287, hlam, p573_0]
                            · have p573_0 := h573c.1
                              have p573_1 := h573c.2.1
                              have p573_2 := h573c.2.2.1
                              have p573_3 := h573c.2.2.2
                              linarith only [h387, hlam, p573_0]
                            · have p573_0 := h573c.1
                              have p573_1 := h573c.2.1
                              have p573_2 := h573c.2.2.1
                              have p573_3 := h573c.2.2.2
                              linarith only [h0, hlam, p573_1]
                            · have p573_0 := h573c.1
                              have p573_1 := h573c.2.1
                              have p573_2 := h573c.2.2.1
                              have p573_3 := h573c.2.2.2
                              linarith only [hlam, p573_0]
                            · have p573_0 := h573c.1
                              have p573_1 := h573c.2.1
                              have p573_2 := h573c.2.2.1
                              have p573_3 := h573c.2.2.2
                              linarith only [h436, hlam, p573_0]
                            · have p573_0 := h573c.1
                              have p573_1 := h573c.2.1
                              have p573_2 := h573c.2.2.1
                              have p573_3 := h573c.2.2.2
                              linarith only [h438, hlam, p573_0]
                            · have p573_0 := h573c.1
                              have p573_1 := h573c.2.1
                              have p573_2 := h573c.2.2.1
                              have p573_3 := h573c.2.2.2
                              linarith only [h440, hlam, p573_0]
                            · have p573_0 := h573c.1
                              have p573_1 := h573c.2.1
                              have p573_2 := h573c.2.2.1
                              have p573_3 := h573c.2.2.2
                              linarith only [hc02, hc23, hlam, hphi, p573_1]
                            · have p573_0 := h573c.1
                              have p573_1 := h573c.2.1
                              have p573_2 := h573c.2.2.1
                              have p573_3 := h573c.2.2.2
                              linarith only [hc12, hc23, hlam, hphi, p573_1]
                            · have p573_0 := h573c.1
                              have p573_1 := h573c.2.1
                              have p573_2 := h573c.2.2.1
                              have p573_3 := h573c.2.2.2
                              linarith only [hlam, p573_0]
                            · have p573_0 := h573c.1
                              have p573_1 := h573c.2.1
                              have p573_2 := h573c.2.2.1
                              have p573_3 := h573c.2.2.2
                              linarith only [h566, h570, h571, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p573_1, u3ehi1]
                            · have p573_0 := h573c.1
                              have p573_1 := h573c.2.1
                              have p573_2 := h573c.2.2.1
                              have p573_3 := h573c.2.2.2
                              linarith only [h566, h570, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p573_1, u3ehi1]
                            · have p573_0 := h573c.1
                              have p573_1 := h573c.2.1
                              have p573_2 := h573c.2.2.1
                              have p573_3 := h573c.2.2.2
                              linarith only [h0, hc12, hc24, hlam, hphi, p573_1]
                            · have p573_0 := h573c.1
                              have p573_1 := h573c.2.1
                              have p573_2 := h573c.2.2.1
                              have p573_3 := h573c.2.2.2
                              linarith only [hc12, hc24, hlam, hphi, p573_1]
                            · have p573_0 := h573c.1
                              have p573_1 := h573c.2.1
                              have p573_2 := h573c.2.2.1
                              have p573_3 := h573c.2.2.2
                              linarith only [h569, hlam, p573_0]
                            · have p573_0 := h573c.1
                              have p573_1 := h573c.2.1
                              have p573_2 := h573c.2.2.1
                              have p573_3 := h573c.2.2.2
                              linarith only [hlam, p573_0]
                            · have p573_0 := h573c.1
                              have p573_1 := h573c.2.1
                              have p573_2 := h573c.2.2.1
                              have p573_3 := h573c.2.2.2
                              linarith only [h566, h570, hc24, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, p573_1, u3ehi1]
                            · have p573_0 := h573c.1
                              have p573_1 := h573c.2.1
                              have p573_2 := h573c.2.2.1
                              have p573_3 := h573c.2.2.2
                              linarith only [h0, hc12, hc25, hlam, hphi, p573_1]
                            · have p573_0 := h573c.1
                              have p573_1 := h573c.2.1
                              have p573_2 := h573c.2.2.1
                              have p573_3 := h573c.2.2.2
                              linarith only [hc12, hc25, hlam, hphi, p573_1]
                            · have p573_0 := h573c.1
                              have p573_1 := h573c.2.1
                              have p573_2 := h573c.2.2.1
                              have p573_3 := h573c.2.2.2
                              linarith only [h570, hlam, p573_0]
                            · have p573_0 := h573c.1
                              have p573_1 := h573c.2.1
                              have p573_2 := h573c.2.2.1
                              have p573_3 := h573c.2.2.2
                              linarith only [h571, hlam, p573_1]
                            · have p573_0 := h573c.1
                              have p573_1 := h573c.2.1
                              have p573_2 := h573c.2.2.1
                              have p573_3 := h573c.2.2.2
                              linarith only [hlam, p573_0]
                          · linarith only [h442, h568, h572, hlam]
                        · linarith only [h0, h287, h442, h568, h569, h571, hc12, hc23, hlam, hphi]
                      · linarith only [h569, h570, hc35, hlam, hphi, u3ehi3]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h602 | h602
                      · linarith only [h569, h602, hc34, hlam, hphi, u3ehi4]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h604 | h604
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h605 | h605
                          · rcases h2bigk with h606c | h606c | h606c | h606c | h606c | h606c | h606c | h606c | h606c | h606c | h606c | h606c | h606c | h606c | h606c | h606c | h606c | h606c | h606c | h606c | h606c | h606c | h606c | h606c | h606c
                            · have p606_0 := h606c.1
                              have p606_1 := h606c.2.1
                              have p606_2 := h606c.2.2.1
                              have p606_3 := h606c.2.2.2
                              linarith only [hlam, p606_0]
                            · have p606_0 := h606c.1
                              have p606_1 := h606c.2.1
                              have p606_2 := h606c.2.2.1
                              have p606_3 := h606c.2.2.2
                              linarith only [h1, hc12, hc23, hlam, hphi, p606_1]
                            · have p606_0 := h606c.1
                              have p606_1 := h606c.2.1
                              have p606_2 := h606c.2.2.1
                              have p606_3 := h606c.2.2.2
                              linarith only [h1, hlam, p606_0]
                            · have p606_0 := h606c.1
                              have p606_1 := h606c.2.1
                              have p606_2 := h606c.2.2.1
                              have p606_3 := h606c.2.2.2
                              linarith only [h287, hlam, p606_0]
                            · have p606_0 := h606c.1
                              have p606_1 := h606c.2.1
                              have p606_2 := h606c.2.2.1
                              have p606_3 := h606c.2.2.2
                              linarith only [h387, hlam, p606_0]
                            · have p606_0 := h606c.1
                              have p606_1 := h606c.2.1
                              have p606_2 := h606c.2.2.1
                              have p606_3 := h606c.2.2.2
                              linarith only [h0, hlam, p606_1]
                            · have p606_0 := h606c.1
                              have p606_1 := h606c.2.1
                              have p606_2 := h606c.2.2.1
                              have p606_3 := h606c.2.2.2
                              linarith only [hlam, p606_0]
                            · have p606_0 := h606c.1
                              have p606_1 := h606c.2.1
                              have p606_2 := h606c.2.2.1
                              have p606_3 := h606c.2.2.2
                              linarith only [h436, hlam, p606_0]
                            · have p606_0 := h606c.1
                              have p606_1 := h606c.2.1
                              have p606_2 := h606c.2.2.1
                              have p606_3 := h606c.2.2.2
                              linarith only [h438, hlam, p606_0]
                            · have p606_0 := h606c.1
                              have p606_1 := h606c.2.1
                              have p606_2 := h606c.2.2.1
                              have p606_3 := h606c.2.2.2
                              linarith only [h440, hlam, p606_0]
                            · have p606_0 := h606c.1
                              have p606_1 := h606c.2.1
                              have p606_2 := h606c.2.2.1
                              have p606_3 := h606c.2.2.2
                              linarith only [hc02, hc23, hlam, hphi, p606_1]
                            · have p606_0 := h606c.1
                              have p606_1 := h606c.2.1
                              have p606_2 := h606c.2.2.1
                              have p606_3 := h606c.2.2.2
                              linarith only [h602, h605, hc12, hc34, hlam, hphi, ht23, p606_1]
                            · have p606_0 := h606c.1
                              have p606_1 := h606c.2.1
                              have p606_2 := h606c.2.2.1
                              have p606_3 := h606c.2.2.2
                              linarith only [hlam, p606_0]
                            · have p606_0 := h606c.1
                              have p606_1 := h606c.2.1
                              have p606_2 := h606c.2.2.1
                              have p606_3 := h606c.2.2.2
                              linarith only [h569, hlam, p606_1]
                            · have p606_0 := h606c.1
                              have p606_1 := h606c.2.1
                              have p606_2 := h606c.2.2.1
                              have p606_3 := h606c.2.2.2
                              linarith only [h602, hlam, p606_1]
                            · have p606_0 := h606c.1
                              have p606_1 := h606c.2.1
                              have p606_2 := h606c.2.2.1
                              have p606_3 := h606c.2.2.2
                              linarith only [h0, hc12, hc24, hlam, hphi, p606_1]
                            · have p606_0 := h606c.1
                              have p606_1 := h606c.2.1
                              have p606_2 := h606c.2.2.1
                              have p606_3 := h606c.2.2.2
                              linarith only [hc12, hc24, hlam, hphi, p606_1]
                            · have p606_0 := h606c.1
                              have p606_1 := h606c.2.1
                              have p606_2 := h606c.2.2.1
                              have p606_3 := h606c.2.2.2
                              linarith only [h1, h569, hc34, hlam, hphi, p606_1, u3ehi0]
                            · have p606_0 := h606c.1
                              have p606_1 := h606c.2.1
                              have p606_2 := h606c.2.2.1
                              have p606_3 := h606c.2.2.2
                              linarith only [hlam, p606_0]
                            · have p606_0 := h606c.1
                              have p606_1 := h606c.2.1
                              have p606_2 := h606c.2.2.1
                              have p606_3 := h606c.2.2.2
                              linarith only [h0, h387, h569, hc12, hc34, hlam, hphi, ht23, p606_1]
                            · have p606_0 := h606c.1
                              have p606_1 := h606c.2.1
                              have p606_2 := h606c.2.2.1
                              have p606_3 := h606c.2.2.2
                              linarith only [h0, hc12, hc25, hlam, hphi, p606_1]
                            · have p606_0 := h606c.1
                              have p606_1 := h606c.2.1
                              have p606_2 := h606c.2.2.1
                              have p606_3 := h606c.2.2.2
                              linarith only [hc12, hc25, hlam, hphi, p606_1]
                            · have p606_0 := h606c.1
                              have p606_1 := h606c.2.1
                              have p606_2 := h606c.2.2.1
                              have p606_3 := h606c.2.2.2
                              linarith only [h0, h1, h602, h605, hc12, hc34, hlam, hphi, ht23, p606_1]
                            · have p606_0 := h606c.1
                              have p606_1 := h606c.2.1
                              have p606_2 := h606c.2.2.1
                              have p606_3 := h606c.2.2.2
                              linarith only [h604, hlam, p606_1]
                            · have p606_0 := h606c.1
                              have p606_1 := h606c.2.1
                              have p606_2 := h606c.2.2.1
                              have p606_3 := h606c.2.2.2
                              linarith only [hlam, p606_0]
                          · linarith only [h438, h568, h569, h605, hlam]
                        · linarith only [h438, h568, h604, hlam]
                  · rcases m.htr 2 3 4 (by decide) (by decide) with h634 | h634
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h635 | h635
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h636 | h636
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h637 | h637
                          · linarith only [h442, h568, h637, hc34, hlam, hphi, u3ehi1]
                          · linarith only [h442, h634, h636, h637, hc23, hlam, hphi, ht01, ht0b, ht12, ht34, ht45, ht5b, u3ehi1]
                        · linarith only [h442, h634, h636, hc45, hlam, hphi, ht34, u3ehi1]
                      · linarith only [h442, h634, h635, hc35, hlam, hphi, u3ehi1]
                    · rcases m.htr 2 3 5 (by decide) (by decide) with h642 | h642
                      · linarith only [h634, h642, hc34, hlam, hphi, u3ehi4]
                      · rcases m.htr 2 4 5 (by decide) (by decide) with h644 | h644
                        · linarith only [h442, h568, h634, h644, hc34, hlam, hphi, u3ehi1]
                        · rcases m.htr 3 4 5 (by decide) (by decide) with h646 | h646
                          · linarith only [h634, h644, h646, hc34, hlam, hphi, u3ehi2]
                          · linarith only [h442, h646, hc45, hlam, hphi, ht34, u3ehi1]

end R2N4
