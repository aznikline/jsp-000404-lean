import Jsp000404.S7N7Defs

set_option maxHeartbeats 1600000

namespace R2N4


theorem r1l7_10_12_13_25_L_R_L_R_L_I_M_IR (m : N7Model)
    (hb0 : CMSig1_7_L_R m.lam m.p (m.t 0) (m.d 0 1) (m.d 0 2) (m.d 0 3) (m.d 0 4) (m.d 0 5))
    (hb2 : CMSig1_7_L_R m.lam m.p (m.t 2) (m.d 0 2) (m.d 1 2) (m.d 2 3) (m.d 2 4) (m.d 2 5))
    (hb3 : CMSig1_7_L_I m.lam m.p (m.t 3) (m.d 0 3) (m.d 1 3) (m.d 2 3) (m.d 3 4) (m.d 3 5))
    (hb5 : CMSig2_7_M_IR m.lam m.p (m.t 5) (m.d 0 5) (m.d 1 5) (m.d 2 5) (m.d 3 5) (m.d 4 5))
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
  have hc34 := m.hcor 3 4 (by decide)
  have hc35 := m.hcor 3 5 (by decide)
  have hc45 := m.hcor 4 5 (by decide)
  have ht01 : m.t 0 < m.t 1 := m.ht (by decide)
  have ht12 : m.t 1 < m.t 2 := m.ht (by decide)
  have ht23 : m.t 2 < m.t 3 := m.ht (by decide)
  have ht34 : m.t 3 < m.t 4 := m.ht (by decide)
  have ht45 : m.t 4 < m.t 5 := m.ht (by decide)
  have h0ehi := hb0.1
  have h2ehi := hb2.1
  have h3bigk := hb3.1
  have h5ehi := hb5.2.1
  have u0ehi0 := h0ehi (m.d 0 1) (by simp)
  have u0ehi1 := h0ehi (m.d 0 2) (by simp)
  have u0ehi2 := h0ehi (m.d 0 3) (by simp)
  have u2ehi0 := h2ehi (m.d 0 2) (by simp)
  have u2ehi1 := h2ehi (m.d 1 2) (by simp)
  have u2ehi2 := h2ehi (m.d 2 3) (by simp)
  have u2ehi3 := h2ehi (m.d 2 4) (by simp)
  have u5ehi1 := h5ehi (m.d 1 5) (by simp)
  have u5ehi2 := h5ehi (m.d 2 5) (by simp)
  have u5ehi3 := h5ehi (m.d 3 5) (by simp)
  have u5ehi4 := h5ehi (m.d 4 5) (by simp)
  rcases m.htr 0 1 2 (by decide) (by decide) with h0 | h0
  · rcases m.htr 0 1 3 (by decide) (by decide) with h1 | h1
    · rcases m.htr 0 2 3 (by decide) (by decide) with h2 | h2
      · rcases m.htr 0 3 5 (by decide) (by decide) with h3 | h3
        · rcases m.htr 1 2 3 (by decide) (by decide) with h4 | h4
          · rcases m.htr 1 2 4 (by decide) (by decide) with h5 | h5
            · rcases m.htr 1 3 5 (by decide) (by decide) with h6 | h6
              · rcases m.htr 2 3 4 (by decide) (by decide) with h7 | h7
                · rcases m.htr 2 3 5 (by decide) (by decide) with h8 | h8
                  · linarith only [h0, h4, h8, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                  · linarith only [h0, h4, h6, h7, h8, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi3]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h11 | h11
                  · linarith only [h0, h11, h4, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                  · linarith only [h0, h11, h4, h6, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h14 | h14
                · rcases m.htr 2 3 5 (by decide) (by decide) with h15 | h15
                  · linarith only [h0, h15, h4, h6, hc01, hc13, hlam, hphi, ht0b, ht34, ht45, ht5b]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h17 | h17
                    · linarith only [h0, h14, h17, h2, h3, h4, h6, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h19 | h19
                      · linarith only [h0, h14, h17, h19, h2, h3, h4, h6, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
                      · rcases h3bigk with h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c | h21c
                        · have p21_0 := h21c.1
                          have p21_1 := h21c.2.1
                          have p21_2 := h21c.2.2.1
                          have p21_3 := h21c.2.2.2
                          linarith only [hlam, p21_0]
                        · have p21_0 := h21c.1
                          have p21_1 := h21c.2.1
                          have p21_2 := h21c.2.2.1
                          have p21_3 := h21c.2.2.2
                          rcases p21_3 (m.d 0 3) (by simp) with h23 | h23
                          · rcases p21_3 (m.d 1 3) (by simp) with h24 | h24
                            · linarith only [h1, h24, hlam]
                            · rcases p21_3 (m.d 2 3) (by simp) with h26 | h26
                              · linarith only [h2, h26, hlam]
                              · rcases p21_3 (m.d 3 4) (by simp) with h28 | h28
                                · linarith only [h14, h28, h3, h4, h6, hlam]
                                · rcases p21_3 (m.d 3 5) (by simp) with h30 | h30
                                  · linarith only [h3, h30, hlam]
                                  · linarith only [h30, h6, hlam]
                          · linarith only [h1, h23, hlam]
                        · have p21_0 := h21c.1
                          have p21_1 := h21c.2.1
                          have p21_2 := h21c.2.2.1
                          have p21_3 := h21c.2.2.2
                          rcases p21_3 (m.d 0 3) (by simp) with h34 | h34
                          · rcases p21_3 (m.d 1 3) (by simp) with h35 | h35
                            · linarith only [h1, h35, hlam]
                            · linarith only [h35, h4, hlam]
                          · linarith only [h2, h34, hlam]
                        · have p21_0 := h21c.1
                          have p21_1 := h21c.2.1
                          have p21_2 := h21c.2.2.1
                          have p21_3 := h21c.2.2.2
                          linarith only [h14, h3, h4, h6, hlam, p21_2]
                        · have p21_0 := h21c.1
                          have p21_1 := h21c.2.1
                          have p21_2 := h21c.2.2.1
                          have p21_3 := h21c.2.2.2
                          linarith only [h0, h14, h2, h4, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p21_1]
                        · have p21_0 := h21c.1
                          have p21_1 := h21c.2.1
                          have p21_2 := h21c.2.2.1
                          have p21_3 := h21c.2.2.2
                          linarith only [h1, hlam, p21_0]
                        · have p21_0 := h21c.1
                          have p21_1 := h21c.2.1
                          have p21_2 := h21c.2.2.1
                          have p21_3 := h21c.2.2.2
                          linarith only [hlam, p21_0]
                        · have p21_0 := h21c.1
                          have p21_1 := h21c.2.1
                          have p21_2 := h21c.2.2.1
                          have p21_3 := h21c.2.2.2
                          linarith only [h14, h6, hc34, hc35, hlam, hphi, ht01, ht0b, ht12, ht23, ht45, ht5b, p21_1]
                        · have p21_0 := h21c.1
                          have p21_1 := h21c.2.1
                          have p21_2 := h21c.2.2.1
                          have p21_3 := h21c.2.2.2
                          linarith only [h0, h2, h3, h6, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p21_1]
                        · have p21_0 := h21c.1
                          have p21_1 := h21c.2.1
                          have p21_2 := h21c.2.2.1
                          have p21_3 := h21c.2.2.2
                          linarith only [h6, hlam, p21_0]
                        · have p21_0 := h21c.1
                          have p21_1 := h21c.2.1
                          have p21_2 := h21c.2.2.1
                          have p21_3 := h21c.2.2.2
                          linarith only [h2, hlam, p21_0]
                        · have p21_0 := h21c.1
                          have p21_1 := h21c.2.1
                          have p21_2 := h21c.2.2.1
                          have p21_3 := h21c.2.2.2
                          linarith only [h4, hlam, p21_0]
                        · have p21_0 := h21c.1
                          have p21_1 := h21c.2.1
                          have p21_2 := h21c.2.2.1
                          have p21_3 := h21c.2.2.2
                          linarith only [hlam, p21_0]
                        · have p21_0 := h21c.1
                          have p21_1 := h21c.2.1
                          have p21_2 := h21c.2.2.1
                          have p21_3 := h21c.2.2.2
                          linarith only [h0, h4, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p21_1]
                        · have p21_0 := h21c.1
                          have p21_1 := h21c.2.1
                          have p21_2 := h21c.2.2.1
                          have p21_3 := h21c.2.2.2
                          linarith only [h15, hlam, p21_0]
                        · have p21_0 := h21c.1
                          have p21_1 := h21c.2.1
                          have p21_2 := h21c.2.2.1
                          have p21_3 := h21c.2.2.2
                          linarith only [h3, h6, hc13, hc34, hlam, hphi, p21_1]
                        · have p21_0 := h21c.1
                          have p21_1 := h21c.2.1
                          have p21_2 := h21c.2.2.1
                          have p21_3 := h21c.2.2.2
                          linarith only [h14, h4, hlam, p21_1]
                        · have p21_0 := h21c.1
                          have p21_1 := h21c.2.1
                          have p21_2 := h21c.2.2.1
                          have p21_3 := h21c.2.2.2
                          linarith only [h14, hlam, p21_0]
                        · have p21_0 := h21c.1
                          have p21_1 := h21c.2.1
                          have p21_2 := h21c.2.2.1
                          have p21_3 := h21c.2.2.2
                          linarith only [hlam, p21_0]
                        · have p21_0 := h21c.1
                          have p21_1 := h21c.2.1
                          have p21_2 := h21c.2.2.1
                          have p21_3 := h21c.2.2.2
                          linarith only [h19, hlam, p21_1]
                        · have p21_0 := h21c.1
                          have p21_1 := h21c.2.1
                          have p21_2 := h21c.2.2.1
                          have p21_3 := h21c.2.2.2
                          linarith only [h3, hlam, p21_0]
                        · have p21_0 := h21c.1
                          have p21_1 := h21c.2.1
                          have p21_2 := h21c.2.2.1
                          have p21_3 := h21c.2.2.2
                          linarith only [h0, h14, h2, h3, h4, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p21_1, u2ehi3]
                        · have p21_0 := h21c.1
                          have p21_1 := h21c.2.1
                          have p21_2 := h21c.2.2.1
                          have p21_3 := h21c.2.2.2
                          linarith only [h0, h14, h2, h3, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p21_1, u2ehi3]
                        · have p21_0 := h21c.1
                          have p21_1 := h21c.2.1
                          have p21_2 := h21c.2.2.1
                          have p21_3 := h21c.2.2.2
                          rcases p21_3 (m.d 0 3) (by simp) with h59 | h59
                          · rcases p21_3 (m.d 1 3) (by simp) with h60 | h60
                            · linarith only [h6, h60, hlam]
                            · linarith only [h14, h4, h60, hlam]
                          · linarith only [h14, h3, h4, h59, h6, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi1]
                        · have p21_0 := h21c.1
                          have p21_1 := h21c.2.1
                          have p21_2 := h21c.2.2.1
                          have p21_3 := h21c.2.2.2
                          linarith only [hlam, p21_0]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h65 | h65
                  · linarith only [h4, h6, h65, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h67 | h67
                    · linarith only [h0, h5, h67, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h69 | h69
                      · linarith only [h67, h69, hc34, hlam, hphi, ht23, u2ehi3]
                      · linarith only [h14, h69, hc45, hlam, hphi, ht23, ht34, u2ehi2]
            · linarith only [h4, h5, hc24, hlam, hphi, u2ehi2]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h73 | h73
            · linarith only [h4, h73, hc23, hlam, hphi, u2ehi3]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h75 | h75
              · rcases m.htr 2 3 4 (by decide) (by decide) with h76 | h76
                · rcases m.htr 2 3 5 (by decide) (by decide) with h77 | h77
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h78 | h78
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h79 | h79
                      · linarith only [h0, h2, h76, h79, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                      · rcases h3bigk with h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c | h81c
                        · have p81_0 := h81c.1
                          have p81_1 := h81c.2.1
                          have p81_2 := h81c.2.2.1
                          have p81_3 := h81c.2.2.2
                          linarith only [hlam, p81_0]
                        · have p81_0 := h81c.1
                          have p81_1 := h81c.2.1
                          have p81_2 := h81c.2.2.1
                          have p81_3 := h81c.2.2.2
                          linarith only [h75, hc03, hlam, hphi, ht0b, ht5b, p81_1, u5ehi3]
                        · have p81_0 := h81c.1
                          have p81_1 := h81c.2.1
                          have p81_2 := h81c.2.2.1
                          have p81_3 := h81c.2.2.2
                          linarith only [h0, h2, h4, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p81_1, u2ehi1]
                        · have p81_0 := h81c.1
                          have p81_1 := h81c.2.1
                          have p81_2 := h81c.2.2.1
                          have p81_3 := h81c.2.2.2
                          rcases p81_3 (m.d 0 3) (by simp) with h85 | h85
                          · rcases p81_3 (m.d 1 3) (by simp) with h86 | h86
                            · linarith only [h1, h86, hlam]
                            · linarith only [h75, h76, h78, h79, h86, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
                          · linarith only [h85, hlam, p81_0]
                        · have p81_0 := h81c.1
                          have p81_1 := h81c.2.1
                          have p81_2 := h81c.2.2.1
                          have p81_3 := h81c.2.2.2
                          rcases p81_3 (m.d 0 3) (by simp) with h90 | h90
                          · rcases p81_3 (m.d 1 3) (by simp) with h91 | h91
                            · linarith only [h1, h91, hlam]
                            · linarith only [h75, h91, hlam]
                          · linarith only [h90, hlam, p81_0]
                        · have p81_0 := h81c.1
                          have p81_1 := h81c.2.1
                          have p81_2 := h81c.2.2.1
                          have p81_3 := h81c.2.2.2
                          linarith only [h1, hlam, p81_0]
                        · have p81_0 := h81c.1
                          have p81_1 := h81c.2.1
                          have p81_2 := h81c.2.2.1
                          have p81_3 := h81c.2.2.2
                          linarith only [hlam, p81_0]
                        · have p81_0 := h81c.1
                          have p81_1 := h81c.2.1
                          have p81_2 := h81c.2.2.1
                          have p81_3 := h81c.2.2.2
                          linarith only [h4, hlam, p81_1]
                        · have p81_0 := h81c.1
                          have p81_1 := h81c.2.1
                          have p81_2 := h81c.2.2.1
                          have p81_3 := h81c.2.2.2
                          rcases p81_3 (m.d 0 3) (by simp) with h98 | h98
                          · rcases p81_3 (m.d 1 3) (by simp) with h99 | h99
                            · rcases p81_3 (m.d 2 3) (by simp) with h100 | h100
                              · rcases p81_3 (m.d 3 4) (by simp) with h101 | h101
                                · linarith only [h101, hlam, p81_0]
                                · rcases p81_3 (m.d 3 5) (by simp) with h103 | h103
                                  · linarith only [h103, h75, hlam]
                                  · linarith only [h103, h79, hlam]
                              · linarith only [h100, h76, hlam]
                            · linarith only [h99, hlam, p81_0]
                          · linarith only [h98, hc13, hlam, hphi, ht01, p81_1, u0ehi2]
                        · have p81_0 := h81c.1
                          have p81_1 := h81c.2.1
                          have p81_2 := h81c.2.2.1
                          have p81_3 := h81c.2.2.2
                          linarith only [h0, h2, h4, hc01, hlam, hphi, ht0b, ht5b, p81_1, u5ehi3]
                        · have p81_0 := h81c.1
                          have p81_1 := h81c.2.1
                          have p81_2 := h81c.2.2.1
                          have p81_3 := h81c.2.2.2
                          linarith only [h2, hlam, p81_0]
                        · have p81_0 := h81c.1
                          have p81_1 := h81c.2.1
                          have p81_2 := h81c.2.2.1
                          have p81_3 := h81c.2.2.2
                          linarith only [h0, h2, h4, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p81_1, u2ehi1]
                        · have p81_0 := h81c.1
                          have p81_1 := h81c.2.1
                          have p81_2 := h81c.2.2.1
                          have p81_3 := h81c.2.2.2
                          linarith only [hlam, p81_0]
                        · have p81_0 := h81c.1
                          have p81_1 := h81c.2.1
                          have p81_2 := h81c.2.2.1
                          have p81_3 := h81c.2.2.2
                          rcases p81_3 (m.d 0 3) (by simp) with h113 | h113
                          · rcases p81_3 (m.d 1 3) (by simp) with h114 | h114
                            · linarith only [h114, h4, hlam]
                            · linarith only [h0, h114, h2, h75, h76, h78, h79, hc01, hlam, hphi, ht0b, ht5b, u5ehi3]
                          · linarith only [h113, h2, h76, h78, h79, hlam]
                        · have p81_0 := h81c.1
                          have p81_1 := h81c.2.1
                          have p81_2 := h81c.2.2.1
                          have p81_3 := h81c.2.2.2
                          linarith only [h0, h2, hc01, hlam, hphi, ht0b, ht5b, p81_1, u5ehi3]
                        · have p81_0 := h81c.1
                          have p81_1 := h81c.2.1
                          have p81_2 := h81c.2.2.1
                          have p81_3 := h81c.2.2.2
                          linarith only [h2, h76, h78, h79, hlam, p81_1]
                        · have p81_0 := h81c.1
                          have p81_1 := h81c.2.1
                          have p81_2 := h81c.2.2.1
                          have p81_3 := h81c.2.2.2
                          linarith only [h0, h2, h75, h76, h78, h79, hc01, hlam, hphi, ht0b, ht5b, p81_1, u5ehi3]
                        · have p81_0 := h81c.1
                          have p81_1 := h81c.2.1
                          have p81_2 := h81c.2.2.1
                          have p81_3 := h81c.2.2.2
                          linarith only [h76, hlam, p81_0]
                        · have p81_0 := h81c.1
                          have p81_1 := h81c.2.1
                          have p81_2 := h81c.2.2.1
                          have p81_3 := h81c.2.2.2
                          linarith only [hlam, p81_0]
                        · have p81_0 := h81c.1
                          have p81_1 := h81c.2.1
                          have p81_2 := h81c.2.2.1
                          have p81_3 := h81c.2.2.2
                          linarith only [h79, hlam, p81_1]
                        · have p81_0 := h81c.1
                          have p81_1 := h81c.2.1
                          have p81_2 := h81c.2.2.1
                          have p81_3 := h81c.2.2.2
                          linarith only [h3, hlam, p81_0]
                        · have p81_0 := h81c.1
                          have p81_1 := h81c.2.1
                          have p81_2 := h81c.2.2.1
                          have p81_3 := h81c.2.2.2
                          linarith only [h75, hlam, p81_0]
                        · have p81_0 := h81c.1
                          have p81_1 := h81c.2.1
                          have p81_2 := h81c.2.2.1
                          have p81_3 := h81c.2.2.2
                          linarith only [h77, hlam, p81_0]
                        · have p81_0 := h81c.1
                          have p81_1 := h81c.2.1
                          have p81_2 := h81c.2.2.1
                          have p81_3 := h81c.2.2.2
                          linarith only [h1, h75, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p81_1]
                        · have p81_0 := h81c.1
                          have p81_1 := h81c.2.1
                          have p81_2 := h81c.2.2.1
                          have p81_3 := h81c.2.2.2
                          linarith only [hlam, p81_0]
                    · linarith only [h73, h78, hc45, hlam, hphi, ht23, ht34, u2ehi1]
                  · linarith only [h4, h75, h77, hlam]
                · linarith only [h4, h76, hc34, hlam, hphi, ht23, u2ehi1]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h132 | h132
                · rcases m.htr 2 3 5 (by decide) (by decide) with h133 | h133
                  · linarith only [h133, h4, h75, hc23, hlam, hphi, u2ehi1]
                  · linarith only [h0, h133, h2, h3, h4, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi1]
                · linarith only [h132, h4, hc34, hlam, hphi, ht23, u2ehi1]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h137 | h137
          · rcases m.htr 1 2 4 (by decide) (by decide) with h138 | h138
            · rcases m.htr 1 3 5 (by decide) (by decide) with h139 | h139
              · linarith only [h139, h3, hc13, hlam, hphi, ht01, u0ehi2]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h141 | h141
                · rcases m.htr 2 3 5 (by decide) (by decide) with h142 | h142
                  · linarith only [h1, h137, h142, h3, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h144 | h144
                    · linarith only [h0, h137, h141, h144, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h146 | h146
                      · linarith only [h0, h137, h141, h144, h146, hc01, hlam, hphi, ht0b, ht5b, u5ehi2]
                      · rcases h3bigk with h148c | h148c | h148c | h148c | h148c | h148c | h148c | h148c | h148c | h148c | h148c | h148c | h148c | h148c | h148c | h148c | h148c | h148c | h148c | h148c | h148c | h148c | h148c | h148c | h148c
                        · have p148_0 := h148c.1
                          have p148_1 := h148c.2.1
                          have p148_2 := h148c.2.2.1
                          have p148_3 := h148c.2.2.2
                          linarith only [hlam, p148_0]
                        · have p148_0 := h148c.1
                          have p148_1 := h148c.2.1
                          have p148_2 := h148c.2.2.1
                          have p148_3 := h148c.2.2.2
                          linarith only [h146, h3, hc13, hc45, hlam, hphi, ht34, p148_1]
                        · have p148_0 := h148c.1
                          have p148_1 := h148c.2.1
                          have p148_2 := h148c.2.2.1
                          have p148_3 := h148c.2.2.2
                          linarith only [h141, h146, h3, hc45, hlam, hphi, ht23, ht34, p148_1, u2ehi3]
                        · have p148_0 := h148c.1
                          have p148_1 := h148c.2.1
                          have p148_2 := h148c.2.2.1
                          have p148_3 := h148c.2.2.2
                          linarith only [h146, h3, hc34, hc45, hlam, hphi, p148_1]
                        · have p148_0 := h148c.1
                          have p148_1 := h148c.2.1
                          have p148_2 := h148c.2.2.1
                          have p148_3 := h148c.2.2.2
                          linarith only [h3, hlam, p148_0]
                        · have p148_0 := h148c.1
                          have p148_1 := h148c.2.1
                          have p148_2 := h148c.2.2.1
                          have p148_3 := h148c.2.2.2
                          linarith only [h1, hlam, p148_0]
                        · have p148_0 := h148c.1
                          have p148_1 := h148c.2.1
                          have p148_2 := h148c.2.2.1
                          have p148_3 := h148c.2.2.2
                          linarith only [hlam, p148_0]
                        · have p148_0 := h148c.1
                          have p148_1 := h148c.2.1
                          have p148_2 := h148c.2.2.1
                          have p148_3 := h148c.2.2.2
                          linarith only [h1, h141, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p148_1, u2ehi3]
                        · have p148_0 := h148c.1
                          have p148_1 := h148c.2.1
                          have p148_2 := h148c.2.2.1
                          have p148_3 := h148c.2.2.2
                          linarith only [h1, h146, h3, hc34, hc45, hlam, hphi, p148_1]
                        · have p148_0 := h148c.1
                          have p148_1 := h148c.2.1
                          have p148_2 := h148c.2.2.1
                          have p148_3 := h148c.2.2.2
                          linarith only [h139, hlam, p148_0]
                        · have p148_0 := h148c.1
                          have p148_1 := h148c.2.1
                          have p148_2 := h148c.2.2.1
                          have p148_3 := h148c.2.2.2
                          linarith only [h2, hlam, p148_0]
                        · have p148_0 := h148c.1
                          have p148_1 := h148c.2.1
                          have p148_2 := h148c.2.2.1
                          have p148_3 := h148c.2.2.2
                          linarith only [h137, hlam, p148_0]
                        · have p148_0 := h148c.1
                          have p148_1 := h148c.2.1
                          have p148_2 := h148c.2.2.1
                          have p148_3 := h148c.2.2.2
                          linarith only [hlam, p148_0]
                        · have p148_0 := h148c.1
                          have p148_1 := h148c.2.1
                          have p148_2 := h148c.2.2.1
                          have p148_3 := h148c.2.2.2
                          linarith only [h0, h137, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p148_1]
                        · have p148_0 := h148c.1
                          have p148_1 := h148c.2.1
                          have p148_2 := h148c.2.2.1
                          have p148_3 := h148c.2.2.2
                          linarith only [h142, hlam, p148_0]
                        · have p148_0 := h148c.1
                          have p148_1 := h148c.2.1
                          have p148_2 := h148c.2.2.1
                          have p148_3 := h148c.2.2.2
                          linarith only [h1, h137, h141, hc34, hlam, hphi, ht23, p148_1, u2ehi3]
                        · have p148_0 := h148c.1
                          have p148_1 := h148c.2.1
                          have p148_2 := h148c.2.2.1
                          have p148_3 := h148c.2.2.2
                          linarith only [h137, h141, hlam, p148_1]
                        · have p148_0 := h148c.1
                          have p148_1 := h148c.2.1
                          have p148_2 := h148c.2.2.1
                          have p148_3 := h148c.2.2.2
                          linarith only [h141, hlam, p148_0]
                        · have p148_0 := h148c.1
                          have p148_1 := h148c.2.1
                          have p148_2 := h148c.2.2.1
                          have p148_3 := h148c.2.2.2
                          linarith only [hlam, p148_0]
                        · have p148_0 := h148c.1
                          have p148_1 := h148c.2.1
                          have p148_2 := h148c.2.2.1
                          have p148_3 := h148c.2.2.2
                          linarith only [h146, hlam, p148_1]
                        · have p148_0 := h148c.1
                          have p148_1 := h148c.2.1
                          have p148_2 := h148c.2.2.1
                          have p148_3 := h148c.2.2.2
                          linarith only [h1, h137, h141, h146, hc45, hlam, hphi, ht23, ht34, p148_1, u2ehi3]
                        · have p148_0 := h148c.1
                          have p148_1 := h148c.2.1
                          have p148_2 := h148c.2.2.1
                          have p148_3 := h148c.2.2.2
                          linarith only [h137, h141, h146, hc45, hlam, hphi, ht23, ht34, p148_1, u2ehi3]
                        · have p148_0 := h148c.1
                          have p148_1 := h148c.2.1
                          have p148_2 := h148c.2.2.1
                          have p148_3 := h148c.2.2.2
                          linarith only [h141, h146, hc45, hlam, hphi, ht23, ht34, p148_1, u2ehi3]
                        · have p148_0 := h148c.1
                          have p148_1 := h148c.2.1
                          have p148_2 := h148c.2.2.1
                          have p148_3 := h148c.2.2.2
                          rcases p148_3 (m.d 0 3) (by simp) with h172 | h172
                          · linarith only [h172, h3, hlam]
                          · linarith only [h1, h137, h141, h172, hc01, hlam, hphi, u0ehi2]
                        · have p148_0 := h148c.1
                          have p148_1 := h148c.2.1
                          have p148_2 := h148c.2.2.1
                          have p148_3 := h148c.2.2.2
                          linarith only [hlam, p148_0]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h176 | h176
                  · linarith only [h0, h138, h141, h176, h3, hc01, hc03, hlam, hphi, ht0b, ht34, ht45, ht5b]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h178 | h178
                    · linarith only [h0, h138, h178, hc01, hlam, hphi, ht0b, ht5b, u5ehi4]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h180 | h180
                      · linarith only [h141, h178, h180, hc34, hlam, hphi, ht23, u2ehi2]
                      · linarith only [h141, h180, hc45, hlam, hphi, ht23, ht34, u2ehi2]
            · linarith only [h137, h138, hc24, hlam, hphi, u2ehi2]
          · linarith only [h137, h2, h3, hc35, hlam, hphi, ht23, u2ehi1]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h185 | h185
        · rcases m.htr 1 2 3 (by decide) (by decide) with h186 | h186
          · linarith only [h186, h2, hc12, hlam, hphi, ht01, u0ehi1]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h188 | h188
            · linarith only [h0, h188, h2, hc23, hlam, hphi, u2ehi3]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h190 | h190
              · rcases m.htr 2 3 4 (by decide) (by decide) with h191 | h191
                · rcases m.htr 2 3 5 (by decide) (by decide) with h192 | h192
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h193 | h193
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h194 | h194
                      · rcases h3bigk with h195c | h195c | h195c | h195c | h195c | h195c | h195c | h195c | h195c | h195c | h195c | h195c | h195c | h195c | h195c | h195c | h195c | h195c | h195c | h195c | h195c | h195c | h195c | h195c | h195c
                        · have p195_0 := h195c.1
                          have p195_1 := h195c.2.1
                          have p195_2 := h195c.2.2.1
                          have p195_3 := h195c.2.2.2
                          linarith only [hlam, p195_0]
                        · have p195_0 := h195c.1
                          have p195_1 := h195c.2.1
                          have p195_2 := h195c.2.2.1
                          have p195_3 := h195c.2.2.2
                          linarith only [h190, hc03, hlam, hphi, ht0b, ht5b, p195_1, u5ehi3]
                        · have p195_0 := h195c.1
                          have p195_1 := h195c.2.1
                          have p195_2 := h195c.2.2.1
                          have p195_3 := h195c.2.2.2
                          linarith only [h2, hlam, p195_1]
                        · have p195_0 := h195c.1
                          have p195_1 := h195c.2.1
                          have p195_2 := h195c.2.2.1
                          have p195_3 := h195c.2.2.2
                          linarith only [h194, hc03, hlam, hphi, ht0b, ht5b, p195_1, u5ehi4]
                        · have p195_0 := h195c.1
                          have p195_1 := h195c.2.1
                          have p195_2 := h195c.2.2.1
                          have p195_3 := h195c.2.2.2
                          rcases p195_3 (m.d 0 3) (by simp) with h200 | h200
                          · rcases p195_3 (m.d 1 3) (by simp) with h201 | h201
                            · linarith only [h1, h201, hlam]
                            · linarith only [h190, h201, hlam]
                          · linarith only [h200, hlam, p195_0]
                        · have p195_0 := h195c.1
                          have p195_1 := h195c.2.1
                          have p195_2 := h195c.2.2.1
                          have p195_3 := h195c.2.2.2
                          linarith only [h1, hlam, p195_0]
                        · have p195_0 := h195c.1
                          have p195_1 := h195c.2.1
                          have p195_2 := h195c.2.2.1
                          have p195_3 := h195c.2.2.2
                          linarith only [hlam, p195_0]
                        · have p195_0 := h195c.1
                          have p195_1 := h195c.2.1
                          have p195_2 := h195c.2.2.1
                          have p195_3 := h195c.2.2.2
                          linarith only [h186, hlam, p195_1]
                        · have p195_0 := h195c.1
                          have p195_1 := h195c.2.1
                          have p195_2 := h195c.2.2.1
                          have p195_3 := h195c.2.2.2
                          linarith only [h194, hc13, hlam, hphi, ht01, ht0b, ht5b, p195_1, u5ehi4]
                        · have p195_0 := h195c.1
                          have p195_1 := h195c.2.1
                          have p195_2 := h195c.2.2.1
                          have p195_3 := h195c.2.2.2
                          linarith only [h1, h194, hc01, hlam, hphi, ht0b, ht5b, p195_1, u5ehi4]
                        · have p195_0 := h195c.1
                          have p195_1 := h195c.2.1
                          have p195_2 := h195c.2.2.1
                          have p195_3 := h195c.2.2.2
                          linarith only [hc23, hlam, hphi, ht01, ht12, p195_1, u0ehi2]
                        · have p195_0 := h195c.1
                          have p195_1 := h195c.2.1
                          have p195_2 := h195c.2.2.1
                          have p195_3 := h195c.2.2.2
                          linarith only [h186, hc23, hlam, hphi, p195_1, u2ehi1]
                        · have p195_0 := h195c.1
                          have p195_1 := h195c.2.1
                          have p195_2 := h195c.2.2.1
                          have p195_3 := h195c.2.2.2
                          linarith only [hlam, p195_0]
                        · have p195_0 := h195c.1
                          have p195_1 := h195c.2.1
                          have p195_2 := h195c.2.2.1
                          have p195_3 := h195c.2.2.2
                          linarith only [h194, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p195_1, u5ehi4]
                        · have p195_0 := h195c.1
                          have p195_1 := h195c.2.1
                          have p195_2 := h195c.2.2.1
                          have p195_3 := h195c.2.2.2
                          rcases p195_3 (m.d 0 3) (by simp) with h214 | h214
                          · linarith only [h2, h214, hlam]
                          · linarith only [h185, h214, hlam]
                        · have p195_0 := h195c.1
                          have p195_1 := h195c.2.1
                          have p195_2 := h195c.2.2.1
                          have p195_3 := h195c.2.2.2
                          linarith only [h1, h190, h194, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p195_1, u5ehi4]
                        · have p195_0 := h195c.1
                          have p195_1 := h195c.2.1
                          have p195_2 := h195c.2.2.1
                          have p195_3 := h195c.2.2.2
                          linarith only [h190, h191, h194, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p195_1, u5ehi4]
                        · have p195_0 := h195c.1
                          have p195_1 := h195c.2.1
                          have p195_2 := h195c.2.2.1
                          have p195_3 := h195c.2.2.2
                          linarith only [h191, hlam, p195_0]
                        · have p195_0 := h195c.1
                          have p195_1 := h195c.2.1
                          have p195_2 := h195c.2.2.1
                          have p195_3 := h195c.2.2.2
                          linarith only [hlam, p195_0]
                        · have p195_0 := h195c.1
                          have p195_1 := h195c.2.1
                          have p195_2 := h195c.2.2.1
                          have p195_3 := h195c.2.2.2
                          linarith only [h191, h194, hc23, hlam, hphi, ht01, ht0b, ht12, ht5b, p195_1, u5ehi4]
                        · have p195_0 := h195c.1
                          have p195_1 := h195c.2.1
                          have p195_2 := h195c.2.2.1
                          have p195_3 := h195c.2.2.2
                          linarith only [h185, hlam, p195_0]
                        · have p195_0 := h195c.1
                          have p195_1 := h195c.2.1
                          have p195_2 := h195c.2.2.1
                          have p195_3 := h195c.2.2.2
                          linarith only [h190, hlam, p195_0]
                        · have p195_0 := h195c.1
                          have p195_1 := h195c.2.1
                          have p195_2 := h195c.2.2.1
                          have p195_3 := h195c.2.2.2
                          linarith only [h192, hlam, p195_0]
                        · have p195_0 := h195c.1
                          have p195_1 := h195c.2.1
                          have p195_2 := h195c.2.2.1
                          have p195_3 := h195c.2.2.2
                          linarith only [h194, hlam, p195_0]
                        · have p195_0 := h195c.1
                          have p195_1 := h195c.2.1
                          have p195_2 := h195c.2.2.1
                          have p195_3 := h195c.2.2.2
                          linarith only [hlam, p195_0]
                      · rcases h3bigk with h227c | h227c | h227c | h227c | h227c | h227c | h227c | h227c | h227c | h227c | h227c | h227c | h227c | h227c | h227c | h227c | h227c | h227c | h227c | h227c | h227c | h227c | h227c | h227c | h227c
                        · have p227_0 := h227c.1
                          have p227_1 := h227c.2.1
                          have p227_2 := h227c.2.2.1
                          have p227_3 := h227c.2.2.2
                          linarith only [hlam, p227_0]
                        · have p227_0 := h227c.1
                          have p227_1 := h227c.2.1
                          have p227_2 := h227c.2.2.1
                          have p227_3 := h227c.2.2.2
                          linarith only [h190, hc03, hlam, hphi, ht0b, ht5b, p227_1, u5ehi3]
                        · have p227_0 := h227c.1
                          have p227_1 := h227c.2.1
                          have p227_2 := h227c.2.2.1
                          have p227_3 := h227c.2.2.2
                          linarith only [h2, hlam, p227_1]
                        · have p227_0 := h227c.1
                          have p227_1 := h227c.2.1
                          have p227_2 := h227c.2.2.1
                          have p227_3 := h227c.2.2.2
                          rcases p227_3 (m.d 0 3) (by simp) with h231 | h231
                          · rcases p227_3 (m.d 1 3) (by simp) with h232 | h232
                            · linarith only [h1, h232, hlam]
                            · linarith only [h190, h194, h232, hlam]
                          · linarith only [h231, hlam, p227_0]
                        · have p227_0 := h227c.1
                          have p227_1 := h227c.2.1
                          have p227_2 := h227c.2.2.1
                          have p227_3 := h227c.2.2.2
                          rcases p227_3 (m.d 0 3) (by simp) with h236 | h236
                          · rcases p227_3 (m.d 1 3) (by simp) with h237 | h237
                            · linarith only [h1, h237, hlam]
                            · linarith only [h190, h237, hlam]
                          · linarith only [h236, hlam, p227_0]
                        · have p227_0 := h227c.1
                          have p227_1 := h227c.2.1
                          have p227_2 := h227c.2.2.1
                          have p227_3 := h227c.2.2.2
                          linarith only [h1, hlam, p227_0]
                        · have p227_0 := h227c.1
                          have p227_1 := h227c.2.1
                          have p227_2 := h227c.2.2.1
                          have p227_3 := h227c.2.2.2
                          linarith only [hlam, p227_0]
                        · have p227_0 := h227c.1
                          have p227_1 := h227c.2.1
                          have p227_2 := h227c.2.2.1
                          have p227_3 := h227c.2.2.2
                          linarith only [h186, hlam, p227_1]
                        · have p227_0 := h227c.1
                          have p227_1 := h227c.2.1
                          have p227_2 := h227c.2.2.1
                          have p227_3 := h227c.2.2.2
                          rcases p227_3 (m.d 0 3) (by simp) with h244 | h244
                          · rcases p227_3 (m.d 1 3) (by simp) with h245 | h245
                            · rcases p227_3 (m.d 2 3) (by simp) with h246 | h246
                              · rcases p227_3 (m.d 3 4) (by simp) with h247 | h247
                                · linarith only [h247, hlam, p227_0]
                                · rcases p227_3 (m.d 3 5) (by simp) with h249 | h249
                                  · linarith only [h190, h249, hlam]
                                  · linarith only [h194, h249, hlam]
                              · linarith only [h191, h246, hlam]
                            · linarith only [h245, hlam, p227_0]
                          · linarith only [h244, hc13, hlam, hphi, ht01, p227_1, u0ehi2]
                        · have p227_0 := h227c.1
                          have p227_1 := h227c.2.1
                          have p227_2 := h227c.2.2.1
                          have p227_3 := h227c.2.2.2
                          linarith only [h1, hc01, hlam, hphi, ht0b, ht5b, p227_1, u5ehi3]
                        · have p227_0 := h227c.1
                          have p227_1 := h227c.2.1
                          have p227_2 := h227c.2.2.1
                          have p227_3 := h227c.2.2.2
                          linarith only [hc23, hlam, hphi, ht01, ht12, p227_1, u0ehi2]
                        · have p227_0 := h227c.1
                          have p227_1 := h227c.2.1
                          have p227_2 := h227c.2.2.1
                          have p227_3 := h227c.2.2.2
                          linarith only [h186, hc23, hlam, hphi, p227_1, u2ehi1]
                        · have p227_0 := h227c.1
                          have p227_1 := h227c.2.1
                          have p227_2 := h227c.2.2.1
                          have p227_3 := h227c.2.2.2
                          linarith only [hlam, p227_0]
                        · have p227_0 := h227c.1
                          have p227_1 := h227c.2.1
                          have p227_2 := h227c.2.2.1
                          have p227_3 := h227c.2.2.2
                          rcases p227_3 (m.d 0 3) (by simp) with h259 | h259
                          · linarith only [h2, h259, hlam]
                          · linarith only [h1, h190, h194, h259, hlam]
                        · have p227_0 := h227c.1
                          have p227_1 := h227c.2.1
                          have p227_2 := h227c.2.2.1
                          have p227_3 := h227c.2.2.2
                          rcases p227_3 (m.d 0 3) (by simp) with h262 | h262
                          · linarith only [h2, h262, hlam]
                          · linarith only [h185, h262, hlam]
                        · have p227_0 := h227c.1
                          have p227_1 := h227c.2.1
                          have p227_2 := h227c.2.2.1
                          have p227_3 := h227c.2.2.2
                          linarith only [h1, h190, h194, hlam, p227_1]
                        · have p227_0 := h227c.1
                          have p227_1 := h227c.2.1
                          have p227_2 := h227c.2.2.1
                          have p227_3 := h227c.2.2.2
                          linarith only [h190, h194, hlam, p227_1]
                        · have p227_0 := h227c.1
                          have p227_1 := h227c.2.1
                          have p227_2 := h227c.2.2.1
                          have p227_3 := h227c.2.2.2
                          linarith only [h191, hlam, p227_0]
                        · have p227_0 := h227c.1
                          have p227_1 := h227c.2.1
                          have p227_2 := h227c.2.2.1
                          have p227_3 := h227c.2.2.2
                          linarith only [hlam, p227_0]
                        · have p227_0 := h227c.1
                          have p227_1 := h227c.2.1
                          have p227_2 := h227c.2.2.1
                          have p227_3 := h227c.2.2.2
                          linarith only [h194, hlam, p227_1]
                        · have p227_0 := h227c.1
                          have p227_1 := h227c.2.1
                          have p227_2 := h227c.2.2.1
                          have p227_3 := h227c.2.2.2
                          linarith only [h185, hlam, p227_0]
                        · have p227_0 := h227c.1
                          have p227_1 := h227c.2.1
                          have p227_2 := h227c.2.2.1
                          have p227_3 := h227c.2.2.2
                          linarith only [h190, hlam, p227_0]
                        · have p227_0 := h227c.1
                          have p227_1 := h227c.2.1
                          have p227_2 := h227c.2.2.1
                          have p227_3 := h227c.2.2.2
                          linarith only [h192, hlam, p227_0]
                        · have p227_0 := h227c.1
                          have p227_1 := h227c.2.1
                          have p227_2 := h227c.2.2.1
                          have p227_3 := h227c.2.2.2
                          linarith only [h1, h190, hc01, hc34, hlam, hphi, ht0b, ht45, ht5b, p227_1]
                        · have p227_0 := h227c.1
                          have p227_1 := h227c.2.1
                          have p227_2 := h227c.2.2.1
                          have p227_3 := h227c.2.2.2
                          linarith only [hlam, p227_0]
                    · linarith only [h188, h193, hc45, hlam, hphi, ht23, ht34, u2ehi1]
                  · linarith only [h1, h190, h192, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                · linarith only [h191, h2, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi1]
              · linarith only [h185, h186, h190, h2, hc23, hlam, hphi, u2ehi1]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h279 | h279
          · linarith only [h2, h279, hc12, hlam, hphi, ht01, u0ehi1]
          · rcases m.htr 1 2 4 (by decide) (by decide) with h281 | h281
            · linarith only [h0, h2, h281, hc23, hlam, hphi, u2ehi3]
            · rcases m.htr 1 3 5 (by decide) (by decide) with h283 | h283
              · linarith only [h1, h185, h283, hlam]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h285 | h285
                · rcases m.htr 2 3 5 (by decide) (by decide) with h286 | h286
                  · linarith only [h185, h2, h286, hc23, hlam, hphi, u2ehi0]
                  · linarith only [h2, h286, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi1]
                · linarith only [h2, h285, hc34, hlam, hphi, ht01, ht12, ht23, u0ehi1]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h290 | h290
      · linarith only [h0, h1, h290, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h292 | h292
        · rcases m.htr 1 2 3 (by decide) (by decide) with h293 | h293
          · linarith only [h290, h293, hc12, hlam, hphi, ht01, u0ehi1]
          · linarith only [h0, h1, h293, hc23, hlam, hphi, u2ehi1]
        · linarith only [h0, h1, h292, hc35, hlam, hphi, ht23, u2ehi1]
  · rcases m.htr 0 1 3 (by decide) (by decide) with h297 | h297
    · rcases m.htr 0 2 3 (by decide) (by decide) with h298 | h298
      · rcases m.htr 0 3 5 (by decide) (by decide) with h299 | h299
        · rcases m.htr 1 2 3 (by decide) (by decide) with h300 | h300
          · rcases m.htr 1 2 4 (by decide) (by decide) with h301 | h301
            · rcases m.htr 1 3 5 (by decide) (by decide) with h302 | h302
              · linarith only [h0, h297, h302, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi3]
              · linarith only [h0, h297, h299, h300, h302, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
            · linarith only [h0, h297, h299, h301, hc24, hlam, hphi, ht01, ht0b, ht12, ht5b, u5ehi3]
          · linarith only [h0, h297, h298, h299, h300, hc02, hlam, hphi, ht0b, ht5b, u5ehi3]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h307 | h307
          · rcases m.htr 1 2 4 (by decide) (by decide) with h308 | h308
            · rcases m.htr 1 3 5 (by decide) (by decide) with h309 | h309
              · linarith only [h297, h299, h309, hc01, hlam, hphi, u0ehi2]
              · rcases m.htr 2 3 4 (by decide) (by decide) with h311 | h311
                · rcases m.htr 2 3 5 (by decide) (by decide) with h312 | h312
                  · linarith only [h299, h312, hc23, hlam, hphi, ht01, ht12, u0ehi2]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h314 | h314
                    · linarith only [h0, h297, h307, h311, h314, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h316 | h316
                      · linarith only [h0, h297, h307, h311, h314, h316, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi2]
                      · rcases h3bigk with h318c | h318c | h318c | h318c | h318c | h318c | h318c | h318c | h318c | h318c | h318c | h318c | h318c | h318c | h318c | h318c | h318c | h318c | h318c | h318c | h318c | h318c | h318c | h318c | h318c
                        · have p318_0 := h318c.1
                          have p318_1 := h318c.2.1
                          have p318_2 := h318c.2.2.1
                          have p318_3 := h318c.2.2.2
                          linarith only [hlam, p318_0]
                        · have p318_0 := h318c.1
                          have p318_1 := h318c.2.1
                          have p318_2 := h318c.2.2.1
                          have p318_3 := h318c.2.2.2
                          linarith only [h299, hc13, hc35, hlam, hphi, p318_1]
                        · have p318_0 := h318c.1
                          have p318_1 := h318c.2.1
                          have p318_2 := h318c.2.2.1
                          have p318_3 := h318c.2.2.2
                          linarith only [h299, h311, h316, hc45, hlam, hphi, ht23, ht34, p318_1, u2ehi3]
                        · have p318_0 := h318c.1
                          have p318_1 := h318c.2.1
                          have p318_2 := h318c.2.2.1
                          have p318_3 := h318c.2.2.2
                          linarith only [h299, h316, hc34, hc45, hlam, hphi, p318_1]
                        · have p318_0 := h318c.1
                          have p318_1 := h318c.2.1
                          have p318_2 := h318c.2.2.1
                          have p318_3 := h318c.2.2.2
                          linarith only [h299, hlam, p318_0]
                        · have p318_0 := h318c.1
                          have p318_1 := h318c.2.1
                          have p318_2 := h318c.2.2.1
                          have p318_3 := h318c.2.2.2
                          linarith only [h297, hlam, p318_0]
                        · have p318_0 := h318c.1
                          have p318_1 := h318c.2.1
                          have p318_2 := h318c.2.2.1
                          have p318_3 := h318c.2.2.2
                          linarith only [hlam, p318_0]
                        · have p318_0 := h318c.1
                          have p318_1 := h318c.2.1
                          have p318_2 := h318c.2.2.1
                          have p318_3 := h318c.2.2.2
                          linarith only [h297, h311, hc01, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p318_1, u2ehi3]
                        · have p318_0 := h318c.1
                          have p318_1 := h318c.2.1
                          have p318_2 := h318c.2.2.1
                          have p318_3 := h318c.2.2.2
                          linarith only [h0, h297, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p318_1]
                        · have p318_0 := h318c.1
                          have p318_1 := h318c.2.1
                          have p318_2 := h318c.2.2.1
                          have p318_3 := h318c.2.2.2
                          linarith only [h309, hlam, p318_0]
                        · have p318_0 := h318c.1
                          have p318_1 := h318c.2.1
                          have p318_2 := h318c.2.2.1
                          have p318_3 := h318c.2.2.2
                          linarith only [h298, hlam, p318_0]
                        · have p318_0 := h318c.1
                          have p318_1 := h318c.2.1
                          have p318_2 := h318c.2.2.1
                          have p318_3 := h318c.2.2.2
                          linarith only [h307, hlam, p318_0]
                        · have p318_0 := h318c.1
                          have p318_1 := h318c.2.1
                          have p318_2 := h318c.2.2.1
                          have p318_3 := h318c.2.2.2
                          linarith only [hlam, p318_0]
                        · have p318_0 := h318c.1
                          have p318_1 := h318c.2.1
                          have p318_2 := h318c.2.2.1
                          have p318_3 := h318c.2.2.2
                          linarith only [h298, h299, h316, hc34, hc45, hlam, hphi, p318_1]
                        · have p318_0 := h318c.1
                          have p318_1 := h318c.2.1
                          have p318_2 := h318c.2.2.1
                          have p318_3 := h318c.2.2.2
                          linarith only [h312, hlam, p318_0]
                        · have p318_0 := h318c.1
                          have p318_1 := h318c.2.1
                          have p318_2 := h318c.2.2.1
                          have p318_3 := h318c.2.2.2
                          linarith only [hc34, hlam, hphi, ht01, ht12, ht23, p318_1, u0ehi2]
                        · have p318_0 := h318c.1
                          have p318_1 := h318c.2.1
                          have p318_2 := h318c.2.2.1
                          have p318_3 := h318c.2.2.2
                          linarith only [h307, h311, hlam, p318_1]
                        · have p318_0 := h318c.1
                          have p318_1 := h318c.2.1
                          have p318_2 := h318c.2.2.1
                          have p318_3 := h318c.2.2.2
                          linarith only [h311, hlam, p318_0]
                        · have p318_0 := h318c.1
                          have p318_1 := h318c.2.1
                          have p318_2 := h318c.2.2.1
                          have p318_3 := h318c.2.2.2
                          linarith only [hlam, p318_0]
                        · have p318_0 := h318c.1
                          have p318_1 := h318c.2.1
                          have p318_2 := h318c.2.2.1
                          have p318_3 := h318c.2.2.2
                          linarith only [h316, hlam, p318_1]
                        · have p318_0 := h318c.1
                          have p318_1 := h318c.2.1
                          have p318_2 := h318c.2.2.1
                          have p318_3 := h318c.2.2.2
                          linarith only [h0, h297, h307, h311, h316, hc12, hc45, hlam, hphi, ht01, ht23, ht34, p318_1, u0ehi2, u2ehi3]
                        · have p318_0 := h318c.1
                          have p318_1 := h318c.2.1
                          have p318_2 := h318c.2.2.1
                          have p318_3 := h318c.2.2.2
                          linarith only [h307, h311, h316, hc45, hlam, hphi, ht23, ht34, p318_1, u2ehi3]
                        · have p318_0 := h318c.1
                          have p318_1 := h318c.2.1
                          have p318_2 := h318c.2.2.1
                          have p318_3 := h318c.2.2.2
                          linarith only [h311, h316, hc45, hlam, hphi, ht23, ht34, p318_1, u2ehi3]
                        · have p318_0 := h318c.1
                          have p318_1 := h318c.2.1
                          have p318_2 := h318c.2.2.1
                          have p318_3 := h318c.2.2.2
                          rcases p318_3 (m.d 0 3) (by simp) with h342 | h342
                          · linarith only [h299, h342, hlam]
                          · linarith only [h0, h297, h307, h311, h342, hc12, hlam, hphi, ht01, u0ehi2]
                        · have p318_0 := h318c.1
                          have p318_1 := h318c.2.1
                          have p318_2 := h318c.2.2.1
                          have p318_3 := h318c.2.2.2
                          linarith only [hlam, p318_0]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h346 | h346
                  · linarith only [h298, h299, h346, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h348 | h348
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h349 | h349
                      · rcases h3bigk with h350c | h350c | h350c | h350c | h350c | h350c | h350c | h350c | h350c | h350c | h350c | h350c | h350c | h350c | h350c | h350c | h350c | h350c | h350c | h350c | h350c | h350c | h350c | h350c | h350c
                        · have p350_0 := h350c.1
                          have p350_1 := h350c.2.1
                          have p350_2 := h350c.2.2.1
                          have p350_3 := h350c.2.2.2
                          linarith only [hlam, p350_0]
                        · have p350_0 := h350c.1
                          have p350_1 := h350c.2.1
                          have p350_2 := h350c.2.2.1
                          have p350_3 := h350c.2.2.2
                          linarith only [h299, h307, h349, hc34, hlam, hphi, ht23, p350_1, u2ehi2]
                        · have p350_0 := h350c.1
                          have p350_1 := h350c.2.1
                          have p350_2 := h350c.2.2.1
                          have p350_3 := h350c.2.2.2
                          linarith only [h299, h349, hc34, hlam, hphi, ht23, p350_1, u2ehi2]
                        · have p350_0 := h350c.1
                          have p350_1 := h350c.2.1
                          have p350_2 := h350c.2.2.1
                          have p350_3 := h350c.2.2.2
                          linarith only [h299, h349, hlam, p350_1]
                        · have p350_0 := h350c.1
                          have p350_1 := h350c.2.1
                          have p350_2 := h350c.2.2.1
                          have p350_3 := h350c.2.2.2
                          linarith only [h299, hlam, p350_0]
                        · have p350_0 := h350c.1
                          have p350_1 := h350c.2.1
                          have p350_2 := h350c.2.2.1
                          have p350_3 := h350c.2.2.2
                          linarith only [h297, hlam, p350_0]
                        · have p350_0 := h350c.1
                          have p350_1 := h350c.2.1
                          have p350_2 := h350c.2.2.1
                          have p350_3 := h350c.2.2.2
                          linarith only [hlam, p350_0]
                        · have p350_0 := h350c.1
                          have p350_1 := h350c.2.1
                          have p350_2 := h350c.2.2.1
                          have p350_3 := h350c.2.2.2
                          linarith only [h0, h297, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p350_1, u2ehi2]
                        · have p350_0 := h350c.1
                          have p350_1 := h350c.2.1
                          have p350_2 := h350c.2.2.1
                          have p350_3 := h350c.2.2.2
                          linarith only [h0, h297, h299, h349, hc03, hc12, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p350_1]
                        · have p350_0 := h350c.1
                          have p350_1 := h350c.2.1
                          have p350_2 := h350c.2.2.1
                          have p350_3 := h350c.2.2.2
                          linarith only [h309, hlam, p350_0]
                        · have p350_0 := h350c.1
                          have p350_1 := h350c.2.1
                          have p350_2 := h350c.2.2.1
                          have p350_3 := h350c.2.2.2
                          linarith only [h298, hlam, p350_0]
                        · have p350_0 := h350c.1
                          have p350_1 := h350c.2.1
                          have p350_2 := h350c.2.2.1
                          have p350_3 := h350c.2.2.2
                          linarith only [h307, hlam, p350_0]
                        · have p350_0 := h350c.1
                          have p350_1 := h350c.2.1
                          have p350_2 := h350c.2.2.1
                          have p350_3 := h350c.2.2.2
                          linarith only [hlam, p350_0]
                        · have p350_0 := h350c.1
                          have p350_1 := h350c.2.1
                          have p350_2 := h350c.2.2.1
                          have p350_3 := h350c.2.2.2
                          linarith only [h311, hlam, p350_0]
                        · have p350_0 := h350c.1
                          have p350_1 := h350c.2.1
                          have p350_2 := h350c.2.2.1
                          have p350_3 := h350c.2.2.2
                          linarith only [h346, hlam, p350_0]
                        · have p350_0 := h350c.1
                          have p350_1 := h350c.2.1
                          have p350_2 := h350c.2.2.1
                          have p350_3 := h350c.2.2.2
                          linarith only [hc34, hlam, hphi, ht01, ht12, ht23, p350_1, u0ehi2]
                        · have p350_0 := h350c.1
                          have p350_1 := h350c.2.1
                          have p350_2 := h350c.2.2.1
                          have p350_3 := h350c.2.2.2
                          linarith only [h307, hc34, hlam, hphi, ht23, p350_1, u2ehi2]
                        · have p350_0 := h350c.1
                          have p350_1 := h350c.2.1
                          have p350_2 := h350c.2.2.1
                          have p350_3 := h350c.2.2.2
                          linarith only [hc34, hlam, hphi, ht23, p350_1, u2ehi2]
                        · have p350_0 := h350c.1
                          have p350_1 := h350c.2.1
                          have p350_2 := h350c.2.2.1
                          have p350_3 := h350c.2.2.2
                          linarith only [hlam, p350_0]
                        · have p350_0 := h350c.1
                          have p350_1 := h350c.2.1
                          have p350_2 := h350c.2.2.1
                          have p350_3 := h350c.2.2.2
                          linarith only [h0, h297, h299, h307, hc12, hc34, hlam, hphi, ht01, ht23, p350_1, u0ehi2, u2ehi2]
                        · have p350_0 := h350c.1
                          have p350_1 := h350c.2.1
                          have p350_2 := h350c.2.2.1
                          have p350_3 := h350c.2.2.2
                          linarith only [h0, h297, h307, hc12, hc35, hlam, hphi, ht01, ht23, p350_1, u0ehi2, u2ehi2]
                        · have p350_0 := h350c.1
                          have p350_1 := h350c.2.1
                          have p350_2 := h350c.2.2.1
                          have p350_3 := h350c.2.2.2
                          linarith only [h307, hc35, hlam, hphi, ht23, p350_1, u2ehi2]
                        · have p350_0 := h350c.1
                          have p350_1 := h350c.2.1
                          have p350_2 := h350c.2.2.1
                          have p350_3 := h350c.2.2.2
                          linarith only [hc35, hlam, hphi, ht23, p350_1, u2ehi2]
                        · have p350_0 := h350c.1
                          have p350_1 := h350c.2.1
                          have p350_2 := h350c.2.2.1
                          have p350_3 := h350c.2.2.2
                          linarith only [h349, hlam, p350_0]
                        · have p350_0 := h350c.1
                          have p350_1 := h350c.2.1
                          have p350_2 := h350c.2.2.1
                          have p350_3 := h350c.2.2.2
                          linarith only [hlam, p350_0]
                      · linarith only [h308, h311, h348, h349, hc14, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, u2ehi2]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h377 | h377
                      · linarith only [h348, h377, hc34, hlam, hphi, ht23, u2ehi3]
                      · linarith only [h311, h377, hc45, hlam, hphi, ht23, ht34, u2ehi2]
            · linarith only [h0, h308, hc24, hlam, hphi, ht01, ht12, u0ehi0]
          · linarith only [h0, h297, h298, h307, hc02, hlam, hphi, u0ehi2]
      · linarith only [h0, h297, h298, hlam]
    · rcases m.htr 0 2 3 (by decide) (by decide) with h383 | h383
      · rcases m.htr 0 3 5 (by decide) (by decide) with h384 | h384
        · rcases m.htr 1 2 3 (by decide) (by decide) with h385 | h385
          · rcases m.htr 1 2 4 (by decide) (by decide) with h386 | h386
            · rcases m.htr 1 3 5 (by decide) (by decide) with h387 | h387
              · rcases m.htr 2 3 4 (by decide) (by decide) with h388 | h388
                · rcases m.htr 2 3 5 (by decide) (by decide) with h389 | h389
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h390 | h390
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h391 | h391
                      · linarith only [h383, h388, h391, hc02, hlam, hphi, ht0b, ht5b, u5ehi4]
                      · rcases h3bigk with h393c | h393c | h393c | h393c | h393c | h393c | h393c | h393c | h393c | h393c | h393c | h393c | h393c | h393c | h393c | h393c | h393c | h393c | h393c | h393c | h393c | h393c | h393c | h393c | h393c
                        · have p393_0 := h393c.1
                          have p393_1 := h393c.2.1
                          have p393_2 := h393c.2.2.1
                          have p393_3 := h393c.2.2.2
                          linarith only [hlam, p393_0]
                        · have p393_0 := h393c.1
                          have p393_1 := h393c.2.1
                          have p393_2 := h393c.2.2.1
                          have p393_3 := h393c.2.2.2
                          linarith only [h297, hlam, p393_1]
                        · have p393_0 := h393c.1
                          have p393_1 := h393c.2.1
                          have p393_2 := h393c.2.2.1
                          have p393_3 := h393c.2.2.2
                          linarith only [h0, h383, h388, h390, h391, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p393_1]
                        · have p393_0 := h393c.1
                          have p393_1 := h393c.2.1
                          have p393_2 := h393c.2.2.1
                          have p393_3 := h393c.2.2.2
                          rcases p393_3 (m.d 0 3) (by simp) with h397 | h397
                          · rcases p393_3 (m.d 1 3) (by simp) with h398 | h398
                            · rcases p393_3 (m.d 2 3) (by simp) with h399 | h399
                              · linarith only [h383, h399, hlam]
                              · linarith only [h388, h399, hlam]
                            · linarith only [h297, h388, h390, h391, h398, hc01, hc23, hlam, hphi, ht12]
                          · linarith only [h397, hlam, p393_0]
                        · have p393_0 := h393c.1
                          have p393_1 := h393c.2.1
                          have p393_2 := h393c.2.2.1
                          have p393_3 := h393c.2.2.2
                          rcases p393_3 (m.d 0 3) (by simp) with h404 | h404
                          · rcases p393_3 (m.d 1 3) (by simp) with h405 | h405
                            · rcases p393_3 (m.d 2 3) (by simp) with h406 | h406
                              · linarith only [h383, h406, hlam]
                              · linarith only [h389, h406, hlam]
                            · linarith only [h387, h405, hlam]
                          · linarith only [h404, hlam, p393_0]
                        · have p393_0 := h393c.1
                          have p393_1 := h393c.2.1
                          have p393_2 := h393c.2.2.1
                          have p393_3 := h393c.2.2.2
                          linarith only [h385, hc12, hlam, hphi, ht01, p393_1, u0ehi2]
                        · have p393_0 := h393c.1
                          have p393_1 := h393c.2.1
                          have p393_2 := h393c.2.2.1
                          have p393_3 := h393c.2.2.2
                          linarith only [hlam, p393_0]
                        · have p393_0 := h393c.1
                          have p393_1 := h393c.2.1
                          have p393_2 := h393c.2.2.1
                          have p393_3 := h393c.2.2.2
                          linarith only [h385, h388, h390, h391, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p393_1]
                        · have p393_0 := h393c.1
                          have p393_1 := h393c.2.1
                          have p393_2 := h393c.2.2.1
                          have p393_3 := h393c.2.2.2
                          rcases p393_3 (m.d 0 3) (by simp) with h414 | h414
                          · linarith only [h297, h414, hlam]
                          · linarith only [h383, h388, h390, h391, h414, hlam]
                        · have p393_0 := h393c.1
                          have p393_1 := h393c.2.1
                          have p393_2 := h393c.2.2.1
                          have p393_3 := h393c.2.2.2
                          rcases p393_3 (m.d 0 3) (by simp) with h417 | h417
                          · linarith only [h297, h417, hlam]
                          · linarith only [h384, h417, hlam]
                        · have p393_0 := h393c.1
                          have p393_1 := h393c.2.1
                          have p393_2 := h393c.2.2.1
                          have p393_3 := h393c.2.2.2
                          linarith only [h383, hlam, p393_0]
                        · have p393_0 := h393c.1
                          have p393_1 := h393c.2.1
                          have p393_2 := h393c.2.2.1
                          have p393_3 := h393c.2.2.2
                          linarith only [h385, hlam, p393_0]
                        · have p393_0 := h393c.1
                          have p393_1 := h393c.2.1
                          have p393_2 := h393c.2.2.1
                          have p393_3 := h393c.2.2.2
                          linarith only [hlam, p393_0]
                        · have p393_0 := h393c.1
                          have p393_1 := h393c.2.1
                          have p393_2 := h393c.2.2.1
                          have p393_3 := h393c.2.2.2
                          rcases p393_3 (m.d 0 3) (by simp) with h423 | h423
                          · rcases p393_3 (m.d 1 3) (by simp) with h424 | h424
                            · rcases p393_3 (m.d 2 3) (by simp) with h425 | h425
                              · rcases p393_3 (m.d 3 4) (by simp) with h426 | h426
                                · linarith only [h426, hlam, p393_0]
                                · rcases p393_3 (m.d 3 5) (by simp) with h428 | h428
                                  · linarith only [h389, h428, hlam]
                                  · linarith only [h391, h428, hlam]
                              · linarith only [h425, hlam, p393_0]
                            · linarith only [h297, h383, h388, h390, h391, h424, hc03, hlam, hphi, u0ehi0]
                          · linarith only [h0, h383, h388, h390, h391, h423, hc12, hlam, hphi, ht01, u0ehi2]
                        · have p393_0 := h393c.1
                          have p393_1 := h393c.2.1
                          have p393_2 := h393c.2.2.1
                          have p393_3 := h393c.2.2.2
                          linarith only [h0, h383, hc12, hlam, hphi, ht01, ht0b, ht5b, p393_1, u5ehi3]
                        · have p393_0 := h393c.1
                          have p393_1 := h393c.2.1
                          have p393_2 := h393c.2.2.1
                          have p393_3 := h393c.2.2.2
                          linarith only [h383, h388, h390, h391, hlam, p393_1]
                        · have p393_0 := h393c.1
                          have p393_1 := h393c.2.1
                          have p393_2 := h393c.2.2.1
                          have p393_3 := h393c.2.2.2
                          linarith only [h0, h383, h388, h390, h391, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p393_1]
                        · have p393_0 := h393c.1
                          have p393_1 := h393c.2.1
                          have p393_2 := h393c.2.2.1
                          have p393_3 := h393c.2.2.2
                          linarith only [h388, hlam, p393_0]
                        · have p393_0 := h393c.1
                          have p393_1 := h393c.2.1
                          have p393_2 := h393c.2.2.1
                          have p393_3 := h393c.2.2.2
                          linarith only [hlam, p393_0]
                        · have p393_0 := h393c.1
                          have p393_1 := h393c.2.1
                          have p393_2 := h393c.2.2.1
                          have p393_3 := h393c.2.2.2
                          linarith only [h391, hlam, p393_1]
                        · have p393_0 := h393c.1
                          have p393_1 := h393c.2.1
                          have p393_2 := h393c.2.2.1
                          have p393_3 := h393c.2.2.2
                          linarith only [h384, hlam, p393_0]
                        · have p393_0 := h393c.1
                          have p393_1 := h393c.2.1
                          have p393_2 := h393c.2.2.1
                          have p393_3 := h393c.2.2.2
                          linarith only [h387, hlam, p393_0]
                        · have p393_0 := h393c.1
                          have p393_1 := h393c.2.1
                          have p393_2 := h393c.2.2.1
                          have p393_3 := h393c.2.2.2
                          linarith only [h389, hlam, p393_0]
                        · have p393_0 := h393c.1
                          have p393_1 := h393c.2.1
                          have p393_2 := h393c.2.2.1
                          have p393_3 := h393c.2.2.2
                          linarith only [h0, h383, h389, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p393_1]
                        · have p393_0 := h393c.1
                          have p393_1 := h393c.2.1
                          have p393_2 := h393c.2.2.1
                          have p393_3 := h393c.2.2.2
                          linarith only [hlam, p393_0]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h445 | h445
                      · linarith only [h390, h445, hc34, hlam, hphi, ht23, u2ehi3]
                      · rcases h3bigk with h447c | h447c | h447c | h447c | h447c | h447c | h447c | h447c | h447c | h447c | h447c | h447c | h447c | h447c | h447c | h447c | h447c | h447c | h447c | h447c | h447c | h447c | h447c | h447c | h447c
                        · have p447_0 := h447c.1
                          have p447_1 := h447c.2.1
                          have p447_2 := h447c.2.2.1
                          have p447_3 := h447c.2.2.2
                          linarith only [hlam, p447_0]
                        · have p447_0 := h447c.1
                          have p447_1 := h447c.2.1
                          have p447_2 := h447c.2.2.1
                          have p447_3 := h447c.2.2.2
                          linarith only [h297, hlam, p447_1]
                        · have p447_0 := h447c.1
                          have p447_1 := h447c.2.1
                          have p447_2 := h447c.2.2.1
                          have p447_3 := h447c.2.2.2
                          linarith only [h297, h389, hc13, hlam, hphi, ht01, ht0b, ht5b, p447_1, u5ehi3]
                        · have p447_0 := h447c.1
                          have p447_1 := h447c.2.1
                          have p447_2 := h447c.2.2.1
                          have p447_3 := h447c.2.2.2
                          rcases p447_3 (m.d 0 3) (by simp) with h451 | h451
                          · rcases p447_3 (m.d 1 3) (by simp) with h452 | h452
                            · rcases p447_3 (m.d 2 3) (by simp) with h453 | h453
                              · linarith only [h383, h453, hlam]
                              · linarith only [h388, h453, hlam]
                            · linarith only [h297, h383, h389, h445, h452, hc02, hlam, hphi, u0ehi0]
                          · linarith only [h451, hlam, p447_0]
                        · have p447_0 := h447c.1
                          have p447_1 := h447c.2.1
                          have p447_2 := h447c.2.2.1
                          have p447_3 := h447c.2.2.2
                          rcases p447_3 (m.d 0 3) (by simp) with h458 | h458
                          · rcases p447_3 (m.d 1 3) (by simp) with h459 | h459
                            · rcases p447_3 (m.d 2 3) (by simp) with h460 | h460
                              · linarith only [h383, h460, hlam]
                              · linarith only [h389, h460, hlam]
                            · linarith only [h387, h459, hlam]
                          · linarith only [h458, hlam, p447_0]
                        · have p447_0 := h447c.1
                          have p447_1 := h447c.2.1
                          have p447_2 := h447c.2.2.1
                          have p447_3 := h447c.2.2.2
                          linarith only [hc13, hlam, hphi, ht01, p447_1, u0ehi2]
                        · have p447_0 := h447c.1
                          have p447_1 := h447c.2.1
                          have p447_2 := h447c.2.2.1
                          have p447_3 := h447c.2.2.2
                          linarith only [hlam, p447_0]
                        · have p447_0 := h447c.1
                          have p447_1 := h447c.2.1
                          have p447_2 := h447c.2.2.1
                          have p447_3 := h447c.2.2.2
                          linarith only [h385, h389, hc12, hlam, hphi, ht01, ht0b, ht5b, p447_1, u5ehi3]
                        · have p447_0 := h447c.1
                          have p447_1 := h447c.2.1
                          have p447_2 := h447c.2.2.1
                          have p447_3 := h447c.2.2.2
                          rcases p447_3 (m.d 0 3) (by simp) with h468 | h468
                          · linarith only [h297, h468, hlam]
                          · linarith only [h383, h388, h468, hlam]
                        · have p447_0 := h447c.1
                          have p447_1 := h447c.2.1
                          have p447_2 := h447c.2.2.1
                          have p447_3 := h447c.2.2.2
                          rcases p447_3 (m.d 0 3) (by simp) with h471 | h471
                          · linarith only [h297, h471, hlam]
                          · linarith only [h384, h471, hlam]
                        · have p447_0 := h447c.1
                          have p447_1 := h447c.2.1
                          have p447_2 := h447c.2.2.1
                          have p447_3 := h447c.2.2.2
                          linarith only [h383, hlam, p447_0]
                        · have p447_0 := h447c.1
                          have p447_1 := h447c.2.1
                          have p447_2 := h447c.2.2.1
                          have p447_3 := h447c.2.2.2
                          linarith only [h385, hlam, p447_0]
                        · have p447_0 := h447c.1
                          have p447_1 := h447c.2.1
                          have p447_2 := h447c.2.2.1
                          have p447_3 := h447c.2.2.2
                          linarith only [hlam, p447_0]
                        · have p447_0 := h447c.1
                          have p447_1 := h447c.2.1
                          have p447_2 := h447c.2.2.1
                          have p447_3 := h447c.2.2.2
                          rcases p447_3 (m.d 0 3) (by simp) with h477 | h477
                          · rcases p447_3 (m.d 1 3) (by simp) with h478 | h478
                            · rcases p447_3 (m.d 2 3) (by simp) with h479 | h479
                              · rcases p447_3 (m.d 3 4) (by simp) with h480 | h480
                                · linarith only [h480, hlam, p447_0]
                                · rcases p447_3 (m.d 3 5) (by simp) with h482 | h482
                                  · linarith only [h389, h482, hlam]
                                  · linarith only [h445, h482, hlam]
                              · linarith only [h479, hlam, p447_0]
                            · linarith only [h297, h383, h478, hc03, hlam, hphi, p447_1, u0ehi0]
                          · linarith only [h0, h383, h477, hc12, hlam, hphi, ht01, p447_1, u0ehi2]
                        · have p447_0 := h447c.1
                          have p447_1 := h447c.2.1
                          have p447_2 := h447c.2.2.1
                          have p447_3 := h447c.2.2.2
                          linarith only [h0, h383, hc12, hlam, hphi, ht01, ht0b, ht5b, p447_1, u5ehi3]
                        · have p447_0 := h447c.1
                          have p447_1 := h447c.2.1
                          have p447_2 := h447c.2.2.1
                          have p447_3 := h447c.2.2.2
                          linarith only [hc34, hlam, hphi, ht01, ht12, ht23, p447_1, u0ehi2]
                        · have p447_0 := h447c.1
                          have p447_1 := h447c.2.1
                          have p447_2 := h447c.2.2.1
                          have p447_3 := h447c.2.2.2
                          linarith only [h297, h387, h445, hc15, hlam, hphi, ht01, p447_1, u0ehi2]
                        · have p447_0 := h447c.1
                          have p447_1 := h447c.2.1
                          have p447_2 := h447c.2.2.1
                          have p447_3 := h447c.2.2.2
                          linarith only [h388, hlam, p447_0]
                        · have p447_0 := h447c.1
                          have p447_1 := h447c.2.1
                          have p447_2 := h447c.2.2.1
                          have p447_3 := h447c.2.2.2
                          linarith only [hlam, p447_0]
                        · have p447_0 := h447c.1
                          have p447_1 := h447c.2.1
                          have p447_2 := h447c.2.2.1
                          have p447_3 := h447c.2.2.2
                          linarith only [h445, hlam, p447_1]
                        · have p447_0 := h447c.1
                          have p447_1 := h447c.2.1
                          have p447_2 := h447c.2.2.1
                          have p447_3 := h447c.2.2.2
                          linarith only [h384, hlam, p447_0]
                        · have p447_0 := h447c.1
                          have p447_1 := h447c.2.1
                          have p447_2 := h447c.2.2.1
                          have p447_3 := h447c.2.2.2
                          linarith only [h387, hlam, p447_0]
                        · have p447_0 := h447c.1
                          have p447_1 := h447c.2.1
                          have p447_2 := h447c.2.2.1
                          have p447_3 := h447c.2.2.2
                          linarith only [h389, hlam, p447_0]
                        · have p447_0 := h447c.1
                          have p447_1 := h447c.2.1
                          have p447_2 := h447c.2.2.1
                          have p447_3 := h447c.2.2.2
                          linarith only [h0, h383, h389, hc12, hc34, hlam, hphi, ht01, ht0b, ht45, ht5b, p447_1]
                        · have p447_0 := h447c.1
                          have p447_1 := h447c.2.1
                          have p447_2 := h447c.2.2.1
                          have p447_3 := h447c.2.2.2
                          linarith only [hlam, p447_0]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h499 | h499
                    · linarith only [h0, h383, h384, h388, h389, h499, hc12, hlam, hphi, ht01, ht0b, ht5b, u5ehi4]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h501 | h501
                      · linarith only [h499, h501, hc34, hlam, hphi, ht23, u2ehi3]
                      · rcases h3bigk with h503c | h503c | h503c | h503c | h503c | h503c | h503c | h503c | h503c | h503c | h503c | h503c | h503c | h503c | h503c | h503c | h503c | h503c | h503c | h503c | h503c | h503c | h503c | h503c | h503c
                        · have p503_0 := h503c.1
                          have p503_1 := h503c.2.1
                          have p503_2 := h503c.2.2.1
                          have p503_3 := h503c.2.2.2
                          linarith only [hlam, p503_0]
                        · have p503_0 := h503c.1
                          have p503_1 := h503c.2.1
                          have p503_2 := h503c.2.2.1
                          have p503_3 := h503c.2.2.2
                          linarith only [h297, hlam, p503_1]
                        · have p503_0 := h503c.1
                          have p503_1 := h503c.2.1
                          have p503_2 := h503c.2.2.1
                          have p503_3 := h503c.2.2.2
                          rcases p503_3 (m.d 0 3) (by simp) with h506 | h506
                          · rcases p503_3 (m.d 1 3) (by simp) with h507 | h507
                            · rcases p503_3 (m.d 2 3) (by simp) with h508 | h508
                              · linarith only [h383, h508, hlam]
                              · rcases p503_3 (m.d 3 4) (by simp) with h510 | h510
                                · linarith only [h384, h388, h389, h510, hlam]
                                · rcases p503_3 (m.d 3 5) (by simp) with h512 | h512
                                  · linarith only [h384, h512, hlam]
                                  · linarith only [h389, h512, hlam]
                            · linarith only [h385, h507, hlam]
                          · linarith only [h383, h506, hlam]
                        · have p503_0 := h503c.1
                          have p503_1 := h503c.2.1
                          have p503_2 := h503c.2.2.1
                          have p503_3 := h503c.2.2.2
                          linarith only [h384, h388, h389, hlam, p503_2]
                        · have p503_0 := h503c.1
                          have p503_1 := h503c.2.1
                          have p503_2 := h503c.2.2.1
                          have p503_3 := h503c.2.2.2
                          linarith only [h0, h383, h388, h389, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p503_1, u2ehi3]
                        · have p503_0 := h503c.1
                          have p503_1 := h503c.2.1
                          have p503_2 := h503c.2.2.1
                          have p503_3 := h503c.2.2.2
                          linarith only [h385, hc12, hlam, hphi, ht01, p503_1, u0ehi2]
                        · have p503_0 := h503c.1
                          have p503_1 := h503c.2.1
                          have p503_2 := h503c.2.2.1
                          have p503_3 := h503c.2.2.2
                          linarith only [hlam, p503_0]
                        · have p503_0 := h503c.1
                          have p503_1 := h503c.2.1
                          have p503_2 := h503c.2.2.1
                          have p503_3 := h503c.2.2.2
                          rcases p503_3 (m.d 0 3) (by simp) with h521 | h521
                          · linarith only [h297, h521, hlam]
                          · linarith only [h383, h521, hlam]
                        · have p503_0 := h503c.1
                          have p503_1 := h503c.2.1
                          have p503_2 := h503c.2.2.1
                          have p503_3 := h503c.2.2.2
                          linarith only [h297, h384, h388, h389, hlam, p503_2]
                        · have p503_0 := h503c.1
                          have p503_1 := h503c.2.1
                          have p503_2 := h503c.2.2.1
                          have p503_3 := h503c.2.2.2
                          linarith only [h388, h389, hc13, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p503_1, u2ehi3]
                        · have p503_0 := h503c.1
                          have p503_1 := h503c.2.1
                          have p503_2 := h503c.2.2.1
                          have p503_3 := h503c.2.2.2
                          linarith only [h383, hlam, p503_0]
                        · have p503_0 := h503c.1
                          have p503_1 := h503c.2.1
                          have p503_2 := h503c.2.2.1
                          have p503_3 := h503c.2.2.2
                          linarith only [h385, hlam, p503_0]
                        · have p503_0 := h503c.1
                          have p503_1 := h503c.2.1
                          have p503_2 := h503c.2.2.1
                          have p503_3 := h503c.2.2.2
                          linarith only [hlam, p503_0]
                        · have p503_0 := h503c.1
                          have p503_1 := h503c.2.1
                          have p503_2 := h503c.2.2.1
                          have p503_3 := h503c.2.2.2
                          linarith only [h384, h389, hc03, hc34, hlam, hphi, ht0b, ht45, ht5b, p503_1]
                        · have p503_0 := h503c.1
                          have p503_1 := h503c.2.1
                          have p503_2 := h503c.2.2.1
                          have p503_3 := h503c.2.2.2
                          linarith only [h389, hlam, p503_0]
                        · have p503_0 := h503c.1
                          have p503_1 := h503c.2.1
                          have p503_2 := h503c.2.2.1
                          have p503_3 := h503c.2.2.2
                          linarith only [h384, h388, h389, hc34, hlam, hphi, ht23, p503_1, u2ehi3]
                        · have p503_0 := h503c.1
                          have p503_1 := h503c.2.1
                          have p503_2 := h503c.2.2.1
                          have p503_3 := h503c.2.2.2
                          linarith only [h0, h383, h384, h388, h389, hc12, hc13, hlam, hphi, ht01, ht0b, ht34, ht45, ht5b, p503_1]
                        · have p503_0 := h503c.1
                          have p503_1 := h503c.2.1
                          have p503_2 := h503c.2.2.1
                          have p503_3 := h503c.2.2.2
                          linarith only [h388, hlam, p503_0]
                        · have p503_0 := h503c.1
                          have p503_1 := h503c.2.1
                          have p503_2 := h503c.2.2.1
                          have p503_3 := h503c.2.2.2
                          linarith only [hlam, p503_0]
                        · have p503_0 := h503c.1
                          have p503_1 := h503c.2.1
                          have p503_2 := h503c.2.2.1
                          have p503_3 := h503c.2.2.2
                          linarith only [h501, hlam, p503_1]
                        · have p503_0 := h503c.1
                          have p503_1 := h503c.2.1
                          have p503_2 := h503c.2.2.1
                          have p503_3 := h503c.2.2.2
                          linarith only [h384, hlam, p503_0]
                        · have p503_0 := h503c.1
                          have p503_1 := h503c.2.1
                          have p503_2 := h503c.2.2.1
                          have p503_3 := h503c.2.2.2
                          linarith only [h387, hlam, p503_0]
                        · have p503_0 := h503c.1
                          have p503_1 := h503c.2.1
                          have p503_2 := h503c.2.2.1
                          have p503_3 := h503c.2.2.2
                          linarith only [h0, h383, h384, h388, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p503_1, u2ehi3]
                        · have p503_0 := h503c.1
                          have p503_1 := h503c.2.1
                          have p503_2 := h503c.2.2.1
                          have p503_3 := h503c.2.2.2
                          rcases p503_3 (m.d 0 3) (by simp) with h539 | h539
                          · rcases p503_3 (m.d 1 3) (by simp) with h540 | h540
                            · rcases p503_3 (m.d 2 3) (by simp) with h541 | h541
                              · linarith only [h389, h541, hlam]
                              · linarith only [h388, h541, hlam]
                            · linarith only [h297, h388, h540, hc23, hlam, hphi, ht01, ht12, u0ehi0]
                          · linarith only [h384, h388, h389, h539, hlam]
                        · have p503_0 := h503c.1
                          have p503_1 := h503c.2.1
                          have p503_2 := h503c.2.2.1
                          have p503_3 := h503c.2.2.2
                          linarith only [hlam, p503_0]
                · rcases m.htr 2 3 5 (by decide) (by decide) with h547 | h547
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h548 | h548
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h549 | h549
                      · rcases h3bigk with h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c | h550c
                        · have p550_0 := h550c.1
                          have p550_1 := h550c.2.1
                          have p550_2 := h550c.2.2.1
                          have p550_3 := h550c.2.2.2
                          linarith only [hlam, p550_0]
                        · have p550_0 := h550c.1
                          have p550_1 := h550c.2.1
                          have p550_2 := h550c.2.2.1
                          have p550_3 := h550c.2.2.2
                          linarith only [h297, hlam, p550_1]
                        · have p550_0 := h550c.1
                          have p550_1 := h550c.2.1
                          have p550_2 := h550c.2.2.1
                          have p550_3 := h550c.2.2.2
                          linarith only [h0, h383, h547, h549, hc12, hlam, hphi, ht01, ht0b, ht5b, p550_1, u5ehi4]
                        · have p550_0 := h550c.1
                          have p550_1 := h550c.2.1
                          have p550_2 := h550c.2.2.1
                          have p550_3 := h550c.2.2.2
                          linarith only [h0, h383, h388, h547, h549, hc12, hlam, hphi, ht01, ht0b, ht5b, p550_1, u5ehi4]
                        · have p550_0 := h550c.1
                          have p550_1 := h550c.2.1
                          have p550_2 := h550c.2.2.1
                          have p550_3 := h550c.2.2.2
                          rcases p550_3 (m.d 0 3) (by simp) with h555 | h555
                          · rcases p550_3 (m.d 1 3) (by simp) with h556 | h556
                            · rcases p550_3 (m.d 2 3) (by simp) with h557 | h557
                              · linarith only [h383, h557, hlam]
                              · linarith only [h547, h557, hlam]
                            · linarith only [h387, h556, hlam]
                          · linarith only [h555, hlam, p550_0]
                        · have p550_0 := h550c.1
                          have p550_1 := h550c.2.1
                          have p550_2 := h550c.2.2.1
                          have p550_3 := h550c.2.2.2
                          linarith only [h385, hc12, hlam, hphi, ht01, p550_1, u0ehi2]
                        · have p550_0 := h550c.1
                          have p550_1 := h550c.2.1
                          have p550_2 := h550c.2.2.1
                          have p550_3 := h550c.2.2.2
                          linarith only [hlam, p550_0]
                        · have p550_0 := h550c.1
                          have p550_1 := h550c.2.1
                          have p550_2 := h550c.2.2.1
                          have p550_3 := h550c.2.2.2
                          linarith only [h385, h547, h549, hc12, hlam, hphi, ht01, ht0b, ht5b, p550_1, u5ehi4]
                        · have p550_0 := h550c.1
                          have p550_1 := h550c.2.1
                          have p550_2 := h550c.2.2.1
                          have p550_3 := h550c.2.2.2
                          linarith only [h385, h388, h547, h549, hc12, hlam, hphi, ht01, ht0b, ht5b, p550_1, u5ehi4]
                        · have p550_0 := h550c.1
                          have p550_1 := h550c.2.1
                          have p550_2 := h550c.2.2.1
                          have p550_3 := h550c.2.2.2
                          rcases p550_3 (m.d 0 3) (by simp) with h566 | h566
                          · linarith only [h297, h566, hlam]
                          · linarith only [h384, h566, hlam]
                        · have p550_0 := h550c.1
                          have p550_1 := h550c.2.1
                          have p550_2 := h550c.2.2.1
                          have p550_3 := h550c.2.2.2
                          linarith only [h383, hlam, p550_0]
                        · have p550_0 := h550c.1
                          have p550_1 := h550c.2.1
                          have p550_2 := h550c.2.2.1
                          have p550_3 := h550c.2.2.2
                          linarith only [h385, hlam, p550_0]
                        · have p550_0 := h550c.1
                          have p550_1 := h550c.2.1
                          have p550_2 := h550c.2.2.1
                          have p550_3 := h550c.2.2.2
                          linarith only [hlam, p550_0]
                        · have p550_0 := h550c.1
                          have p550_1 := h550c.2.1
                          have p550_2 := h550c.2.2.1
                          have p550_3 := h550c.2.2.2
                          linarith only [h388, hlam, p550_0]
                        · have p550_0 := h550c.1
                          have p550_1 := h550c.2.1
                          have p550_2 := h550c.2.2.1
                          have p550_3 := h550c.2.2.2
                          linarith only [h388, h549, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p550_1, u5ehi4]
                        · have p550_0 := h550c.1
                          have p550_1 := h550c.2.1
                          have p550_2 := h550c.2.2.1
                          have p550_3 := h550c.2.2.2
                          linarith only [hc34, hlam, hphi, ht01, ht12, ht23, p550_1, u0ehi2]
                        · have p550_0 := h550c.1
                          have p550_1 := h550c.2.1
                          have p550_2 := h550c.2.2.1
                          have p550_3 := h550c.2.2.2
                          linarith only [h297, hc34, hlam, hphi, ht01, ht12, ht23, p550_1, u0ehi0]
                        · have p550_0 := h550c.1
                          have p550_1 := h550c.2.1
                          have p550_2 := h550c.2.2.1
                          have p550_3 := h550c.2.2.2
                          linarith only [h547, h549, hc34, hlam, hphi, ht01, ht0b, ht12, ht23, ht5b, p550_1, u5ehi4]
                        · have p550_0 := h550c.1
                          have p550_1 := h550c.2.1
                          have p550_2 := h550c.2.2.1
                          have p550_3 := h550c.2.2.2
                          linarith only [hlam, p550_0]
                        · have p550_0 := h550c.1
                          have p550_1 := h550c.2.1
                          have p550_2 := h550c.2.2.1
                          have p550_3 := h550c.2.2.2
                          rcases p550_3 (m.d 0 3) (by simp) with h578 | h578
                          · rcases p550_3 (m.d 1 3) (by simp) with h579 | h579
                            · rcases p550_3 (m.d 2 3) (by simp) with h580 | h580
                              · linarith only [h388, h580, hlam]
                              · linarith only [h547, h580, hlam]
                            · linarith only [h387, h579, hlam]
                          · linarith only [h384, h578, hlam]
                        · have p550_0 := h550c.1
                          have p550_1 := h550c.2.1
                          have p550_2 := h550c.2.2.1
                          have p550_3 := h550c.2.2.2
                          linarith only [h384, hlam, p550_0]
                        · have p550_0 := h550c.1
                          have p550_1 := h550c.2.1
                          have p550_2 := h550c.2.2.1
                          have p550_3 := h550c.2.2.2
                          linarith only [h387, hlam, p550_0]
                        · have p550_0 := h550c.1
                          have p550_1 := h550c.2.1
                          have p550_2 := h550c.2.2.1
                          have p550_3 := h550c.2.2.2
                          linarith only [h547, hlam, p550_0]
                        · have p550_0 := h550c.1
                          have p550_1 := h550c.2.1
                          have p550_2 := h550c.2.2.1
                          have p550_3 := h550c.2.2.2
                          linarith only [h549, hlam, p550_0]
                        · have p550_0 := h550c.1
                          have p550_1 := h550c.2.1
                          have p550_2 := h550c.2.2.1
                          have p550_3 := h550c.2.2.2
                          linarith only [hlam, p550_0]
                      · linarith only [h388, h547, h549, hc45, hlam, hphi, ht01, ht0b, ht12, ht23, ht34, ht5b, u5ehi3]
                    · linarith only [h388, h547, h548, hlam]
                  · rcases m.htr 2 4 5 (by decide) (by decide) with h592 | h592
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h593 | h593
                      · rcases h3bigk with h594c | h594c | h594c | h594c | h594c | h594c | h594c | h594c | h594c | h594c | h594c | h594c | h594c | h594c | h594c | h594c | h594c | h594c | h594c | h594c | h594c | h594c | h594c | h594c | h594c
                        · have p594_0 := h594c.1
                          have p594_1 := h594c.2.1
                          have p594_2 := h594c.2.2.1
                          have p594_3 := h594c.2.2.2
                          linarith only [hlam, p594_0]
                        · have p594_0 := h594c.1
                          have p594_1 := h594c.2.1
                          have p594_2 := h594c.2.2.1
                          have p594_3 := h594c.2.2.2
                          linarith only [h297, hlam, p594_1]
                        · have p594_0 := h594c.1
                          have p594_1 := h594c.2.1
                          have p594_2 := h594c.2.2.1
                          have p594_3 := h594c.2.2.2
                          rcases p594_3 (m.d 0 3) (by simp) with h597 | h597
                          · rcases p594_3 (m.d 1 3) (by simp) with h598 | h598
                            · rcases p594_3 (m.d 2 3) (by simp) with h599 | h599
                              · linarith only [h383, h599, hlam]
                              · rcases p594_3 (m.d 3 4) (by simp) with h601 | h601
                                · linarith only [h384, h547, h601, hc34, hlam, hphi, ht23, u2ehi2]
                                · linarith only [h388, h601, hlam]
                            · linarith only [h385, h598, hlam]
                          · linarith only [h383, h597, hlam]
                        · have p594_0 := h594c.1
                          have p594_1 := h594c.2.1
                          have p594_2 := h594c.2.2.1
                          have p594_3 := h594c.2.2.2
                          linarith only [h388, hc03, hlam, hphi, ht0b, ht23, ht34, ht45, ht5b, p594_1, u2ehi2]
                        · have p594_0 := h594c.1
                          have p594_1 := h594c.2.1
                          have p594_2 := h594c.2.2.1
                          have p594_3 := h594c.2.2.2
                          linarith only [h0, h383, h547, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p594_1, u2ehi2]
                        · have p594_0 := h594c.1
                          have p594_1 := h594c.2.1
                          have p594_2 := h594c.2.2.1
                          have p594_3 := h594c.2.2.2
                          linarith only [hc13, hlam, hphi, ht01, p594_1, u0ehi2]
                        · have p594_0 := h594c.1
                          have p594_1 := h594c.2.1
                          have p594_2 := h594c.2.2.1
                          have p594_3 := h594c.2.2.2
                          linarith only [hlam, p594_0]
                        · have p594_0 := h594c.1
                          have p594_1 := h594c.2.1
                          have p594_2 := h594c.2.2.1
                          have p594_3 := h594c.2.2.2
                          rcases p594_3 (m.d 0 3) (by simp) with h610 | h610
                          · linarith only [h297, h610, hlam]
                          · linarith only [h383, h610, hlam]
                        · have p594_0 := h594c.1
                          have p594_1 := h594c.2.1
                          have p594_2 := h594c.2.2.1
                          have p594_3 := h594c.2.2.2
                          linarith only [h385, h547, h593, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p594_1, u2ehi2]
                        · have p594_0 := h594c.1
                          have p594_1 := h594c.2.1
                          have p594_2 := h594c.2.2.1
                          have p594_3 := h594c.2.2.2
                          linarith only [h385, h547, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p594_1, u2ehi2]
                        · have p594_0 := h594c.1
                          have p594_1 := h594c.2.1
                          have p594_2 := h594c.2.2.1
                          have p594_3 := h594c.2.2.2
                          linarith only [h383, hlam, p594_0]
                        · have p594_0 := h594c.1
                          have p594_1 := h594c.2.1
                          have p594_2 := h594c.2.2.1
                          have p594_3 := h594c.2.2.2
                          linarith only [h385, hlam, p594_0]
                        · have p594_0 := h594c.1
                          have p594_1 := h594c.2.1
                          have p594_2 := h594c.2.2.1
                          have p594_3 := h594c.2.2.2
                          linarith only [hlam, p594_0]
                        · have p594_0 := h594c.1
                          have p594_1 := h594c.2.1
                          have p594_2 := h594c.2.2.1
                          have p594_3 := h594c.2.2.2
                          linarith only [h388, hlam, p594_0]
                        · have p594_0 := h594c.1
                          have p594_1 := h594c.2.1
                          have p594_2 := h594c.2.2.1
                          have p594_3 := h594c.2.2.2
                          linarith only [h547, hlam, p594_0]
                        · have p594_0 := h594c.1
                          have p594_1 := h594c.2.1
                          have p594_2 := h594c.2.2.1
                          have p594_3 := h594c.2.2.2
                          linarith only [h384, h547, hc34, hlam, hphi, ht23, p594_1, u2ehi2]
                        · have p594_0 := h594c.1
                          have p594_1 := h594c.2.1
                          have p594_2 := h594c.2.2.1
                          have p594_3 := h594c.2.2.2
                          linarith only [h297, hc34, hlam, hphi, ht01, ht12, ht23, p594_1, u0ehi0]
                        · have p594_0 := h594c.1
                          have p594_1 := h594c.2.1
                          have p594_2 := h594c.2.2.1
                          have p594_3 := h594c.2.2.2
                          linarith only [hc34, hlam, hphi, ht23, p594_1, u2ehi2]
                        · have p594_0 := h594c.1
                          have p594_1 := h594c.2.1
                          have p594_2 := h594c.2.2.1
                          have p594_3 := h594c.2.2.2
                          linarith only [hlam, p594_0]
                        · have p594_0 := h594c.1
                          have p594_1 := h594c.2.1
                          have p594_2 := h594c.2.2.1
                          have p594_3 := h594c.2.2.2
                          linarith only [h547, hc34, hlam, hphi, ht23, p594_1, u2ehi2]
                        · have p594_0 := h594c.1
                          have p594_1 := h594c.2.1
                          have p594_2 := h594c.2.2.1
                          have p594_3 := h594c.2.2.2
                          linarith only [h384, hlam, p594_0]
                        · have p594_0 := h594c.1
                          have p594_1 := h594c.2.1
                          have p594_2 := h594c.2.2.1
                          have p594_3 := h594c.2.2.2
                          linarith only [h387, hlam, p594_0]
                        · have p594_0 := h594c.1
                          have p594_1 := h594c.2.1
                          have p594_2 := h594c.2.2.1
                          have p594_3 := h594c.2.2.2
                          linarith only [h0, h383, h384, hc12, hlam, hphi, ht01, ht0b, ht23, ht34, ht45, ht5b, p594_1, u2ehi2]
                        · have p594_0 := h594c.1
                          have p594_1 := h594c.2.1
                          have p594_2 := h594c.2.2.1
                          have p594_3 := h594c.2.2.2
                          linarith only [h593, hlam, p594_0]
                        · have p594_0 := h594c.1
                          have p594_1 := h594c.2.1
                          have p594_2 := h594c.2.2.1
                          have p594_3 := h594c.2.2.2
                          linarith only [hlam, p594_0]
                      · linarith only [h388, h592, h593, hc24, hlam, hphi, u2ehi2]
                    · rcases m.htr 3 4 5 (by decide) (by decide) with h631 | h631
                      · linarith only [h592, h631, hc34, hlam, hphi, ht23, u2ehi3]
                      · linarith only [h388, h631, hc45, hlam, hphi, ht23, ht34, u2ehi2]
              · linarith only [h297, h384, h387, hlam]
            · linarith only [h0, h386, hc24, hlam, hphi, ht01, ht12, u0ehi0]
          · linarith only [h0, h385, hc23, hlam, hphi, ht01, ht12, u0ehi0]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h637 | h637
          · rcases m.htr 1 2 4 (by decide) (by decide) with h638 | h638
            · rcases m.htr 1 3 5 (by decide) (by decide) with h639 | h639
              · linarith only [h384, h637, h639, hc12, hlam, hphi, ht01, u0ehi2]
              · linarith only [h297, h639, hc35, hlam, hphi, ht01, ht12, ht23, u0ehi0]
            · linarith only [h0, h638, hc24, hlam, hphi, ht01, ht12, u0ehi0]
          · linarith only [h0, h383, h637, hlam]
      · rcases m.htr 0 3 5 (by decide) (by decide) with h644 | h644
        · rcases m.htr 1 2 3 (by decide) (by decide) with h645 | h645
          · linarith only [h383, h645, hc12, hlam, hphi, ht01, u0ehi1]
          · linarith only [h0, h645, hc23, hlam, hphi, ht01, ht12, u0ehi0]
        · rcases m.htr 1 2 3 (by decide) (by decide) with h648 | h648
          · linarith only [h0, h383, h648, hc12, hlam, hphi, ht01, u0ehi0]
          · linarith only [h0, h648, hc23, hlam, hphi, ht01, ht12, u0ehi0]

end R2N4
